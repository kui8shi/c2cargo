//! LLM analysis module for argument analysis
use futures::StreamExt;
use llm::{
    builder::{LLMBackend, LLMBuilder},
    chat::{ChatMessage, Usage},
};
use serde::{de::DeserializeOwned, Serialize};
use std::time::Duration;
use tokio::time::sleep;

pub(crate) trait LLMAnalysisInput<E>: std::fmt::Debug + Clone + Serialize {
    fn get_evidence_for_validation(&self) -> &E;
}

pub(crate) trait LLMAnalysisOutput<E>:
    std::fmt::Debug + Serialize + DeserializeOwned
{
    fn validate(&self, evidence: &E) -> Result<(), Vec<String>>;

    fn normalize(&mut self) {}
}

// ----- Static schema and prompt (reuse the previous prompt verbatim) -----

pub(crate) trait LLMAnalysis {
    type Evidence;
    type Input: LLMAnalysisInput<Self::Evidence>;
    type Output: LLMAnalysisOutput<Self::Evidence>;

    const MODEL: &str = "gpt-5-nano";

    fn new() -> Self;

    /// Analyze various properties of build options using LLMs
    async fn run_llm_analysis<'a, I: Iterator<Item = &'a Self::Input>>(
        &'a mut self,
        inputs: I,
    ) -> Vec<Self::Output> {
        futures::stream::iter(inputs.map(|input| self.make_api_request_with_retry(input)))
            .buffer_unordered(10)
            .then(|result| async move {
                match result {
                    Ok(analysis) => Some(analysis),
                    Err(e) => {
                        eprintln!("Failed to analyze build option: {}", e);
                        None
                    }
                }
            })
            .filter_map(|opt| async move { opt })
            .collect()
            .await
    }

    fn schema_text(&self) -> &'static str;

    fn extraction_prompt(&self) -> &'static str;

    /// Package the schema + prompt + user fragments into one user message.
    fn compose_user_content(&self, input: &Self::Input) -> String {
        serde_json::json!({
            "schema": serde_json::from_str::<serde_json::Value>(self.schema_text()).unwrap(),
            "instruction": self.extraction_prompt(),
            "input": input
        })
        .to_string()
    }

    fn compose_user_content_with_feedback(
        &self,
        input: &Self::Input,
        prev_json: Option<&str>,
        errors: Option<&[String]>,
    ) -> String {
        let base = self.compose_user_content(input);

        let mut extra = String::new();
        if let Some(j) = prev_json {
            extra.push_str("\n\n# PreviousInvalidJSON\n");
            extra.push_str(j);
            extra.push('\n');
        }
        if let Some(errs) = errors {
            extra.push_str("\n\n# ValidationErrors\n");
            for e in errs {
                extra.push_str("- ");
                extra.push_str(e);
                extra.push('\n');
            }
        }

        format!("{base}{extra}")
    }

    async fn make_api_request_with_retry(
        &self,
        input: &Self::Input,
    ) -> Result<Self::Output, String> {
        const MAX_RETRIES: usize = 3;
        const RETRY_DELAY_MS: u64 = 1000;

        let api_key = std::env::var("OPENAI_API_KEY").unwrap_or("sk-TESTKEY".into());

        // Keep last errors and raw JSON to feed back into the next retry
        let mut last_errors: Option<Vec<String>> = None;
        let mut last_raw_json: Option<String> = None;

        for attempt in 0..MAX_RETRIES {
            let llm = LLMBuilder::new()
                .backend(LLMBackend::OpenAI)
                .api_key(api_key.clone())
                .model(Self::MODEL)
                .stream(false)
                .build()
                .map_err(|e| format!("Failed to build LLM client: {}", e))?;

            // Add validation feedback and previous invalid JSON if available
            let prompt = self.compose_user_content_with_feedback(
                input,
                last_raw_json.as_deref(),
                last_errors.as_deref(),
            );
            let msg = ChatMessage::user().content(prompt).build();

            match llm.chat(&[msg]).await {
                Ok(response) => {
                    let text = response.text().ok_or("No text in response")?;
                    // println!("Raw JSON (attempt {}):\n{}", attempt + 1, text);
                    // if let Some(usage) = response.usage() {
                    //     show_cost(usage);
                    // }

                    match serde_json::from_str::<Self::Output>(&text) {
                        Ok(mut result) => {
                            match result.validate(&input.get_evidence_for_validation()) {
                                Ok(()) => {
                                    result.normalize();
                                    return Ok(result);
                                }
                                Err(errs) => {
                                    last_errors = Some(errs);
                                    last_raw_json = Some(text);
                                    if attempt < MAX_RETRIES - 1 {
                                        // eprintln!("Validation failed; retrying in {}ms...", RETRY_DELAY_MS);
                                        sleep(Duration::from_millis(RETRY_DELAY_MS)).await;
                                        continue;
                                    } else {
                                        return Err(format!(
                                            "Validation failed after {} attempts: {:?}",
                                            MAX_RETRIES, last_errors
                                        ));
                                    }
                                }
                            }
                        }
                        Err(e) => {
                            last_errors = Some(vec![format!("JSON parse error: {}", e)]);
                            last_raw_json = Some(text);
                            if attempt < MAX_RETRIES - 1 {
                                // eprintln!("JSON parse error; retrying in {}ms...", RETRY_DELAY_MS);
                                sleep(Duration::from_millis(RETRY_DELAY_MS)).await;
                                continue;
                            } else {
                                return Err(format!(
                                    "Failed to parse JSON after {} attempts: {}",
                                    MAX_RETRIES, e
                                ));
                            }
                        }
                    }
                }
                Err(e) => {
                    /*
                    eprintln!(
                        "API request error on attempt {} for option '{}': {}",
                        attempt + 1,
                        build_option.option_name,
                        e
                    );
                    */
                    if attempt < MAX_RETRIES - 1 {
                        // eprintln!("Retrying in {}ms...", RETRY_DELAY_MS);
                        sleep(Duration::from_millis(RETRY_DELAY_MS)).await;
                    } else {
                        return Err(format!(
                            "API request failed after {} attempts: {}",
                            MAX_RETRIES, e
                        ));
                    }
                }
            }
        }

        unreachable!()
    }

    fn show_cost(usage: Usage) {
        // Show usage and rough cost estimation

        eprintln!(
            "Usage: prompt={} completion={} total={}",
            usage.prompt_tokens, usage.completion_tokens, usage.total_tokens
        );

        const M: f64 = 1_000_000.;
        // Simple cost estimation (adjust rates to your provider/model)
        let (prompt_rate, completion_rate) = match Self::MODEL {
            // (input, output) USD per 1M token
            "gpt-5" => (1.25, 10.),
            "gpt-5-mini" => (0.25, 2.),
            _ => (0.05, 0.40), // gpt5-nano
        };
        let cost = (usage.prompt_tokens as f64) / M * prompt_rate
            + (usage.completion_tokens as f64) / M * completion_rate;
        eprintln!("Estimated cost: ${:.6}", cost);
    }
}
