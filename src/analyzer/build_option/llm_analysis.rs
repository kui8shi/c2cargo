//! LLM analysis module for argument analysis
use futures::StreamExt;
use llm::{
    builder::{LLMBackend, LLMBuilder},
    chat::{ChatMessage, Usage},
};
use serde::{Deserialize, Serialize};
use std::{collections::HashMap, option, time::Duration};
use tokio::time::sleep;

use super::BuildOption;

// ----- Data types for structured output -----

#[derive(Debug, Serialize, Deserialize)]
pub(super) struct BuildOptionLLMAnalysisResult {
    #[serde(default)]
    /// Distinct literals except yes/no/empty and paths.
    pub representatives: Vec<String>,
    /// Name of the build option
    pub aliases: Option<HashMap<String, String>>,
    /// Whether enabled by default or null if unknown.
    pub enabled_by_default: Option<bool>,
    /// Name of the build option
    pub option_name: String,
}

impl BuildOptionLLMAnalysisResult {
    /// Validate this result against the prompt-defined rules using the provided `values` as Candidates.
    /// Returns `Ok(())` if valid, or `Err(Vec<String>)` with all detected issues.
    fn validate(&self, values: &[String]) -> Result<(), Vec<String>> {
        use std::collections::HashSet;

        let mut errors = Vec::new();

        // Candidates (input "values")
        let candidates: HashSet<String> = values.iter().cloned().collect();

        // Representatives
        let reps_vec = self.representatives.clone();
        let reps_set: HashSet<String> = reps_vec.iter().cloned().collect();

        // 0) Basic sanity on option_name (schema requires string, but ensure non-empty)
        if self.option_name.trim().is_empty() {
            errors.push("option_name must be a non-empty string".to_string());
        }

        // 1) representatives must be unique (schema enforces, but double-check) and subset of candidates
        if reps_vec.len() != reps_set.len() {
            errors.push("representatives must contain unique items".to_string());
        }
        if !reps_set.is_subset(&candidates) {
            let missing: Vec<String> = reps_set.difference(&candidates).cloned().collect();
            errors.push(format!(
                "representatives must be a subset of candidates; not in candidates: {:?}",
                missing
            ));
        }

        // 2a) representatives must not contain some literals
        let banned_reps = ["auto", "detect", "autodetect", "auto-detect"];
        let found_banned: Vec<&str> = banned_reps
            .iter()
            .copied()
            .filter(|b| reps_set.contains(&b.to_string()))
            .collect();
        if !found_banned.is_empty() {
            errors.push(format!(
                "representatives must not include {:?}",
                found_banned
            ));
        }

        // 2b) representatives must not contain yes, no, and other literals.
        if reps_set.contains("yes") && reps_set.contains("no") {
            if reps_set.len() > 2 {
                errors.push(format!(
                    r#"If "yes" and "no" are in representatives, they must not hold any other value: {:?}"#,
                    reps_set.iter().filter(|r| !(matches!(r.as_str(), "yes"|"no"))).collect::<Vec<_>>()
                ))
            }
        }

        // 3) aliases must partition the non-representatives:
        // alias_keys == (candidates - representatives)
        let non_rep: HashSet<String> = candidates.difference(&reps_set).cloned().collect();

        match &self.aliases {
            None => {
                if !non_rep.is_empty() {
                    let mut list: Vec<String> = non_rep.iter().cloned().collect();
                    list.sort();
                    errors.push(format!(
                        "aliases must be present because there are non-representative candidates: {:?}",
                        list
                    ));
                }
            }
            Some(aliases) => {
                // aliases may be null or an object; when object, it must map *all* non-representatives.
                let alias_keys: HashSet<String> = aliases.keys().cloned().collect();

                // 3a) No keys outside candidates
                let outside_candidates: Vec<String> =
                    alias_keys.difference(&candidates).cloned().collect();
                if !outside_candidates.is_empty() {
                    errors.push(format!(
                        "aliases contain keys not in candidates: {:?}",
                        outside_candidates
                    ));
                }

                // 3b) Keys must be exactly the set of non-representatives
                let missing_keys: Vec<String> = non_rep.difference(&alias_keys).cloned().collect();
                let extra_keys: Vec<String> = alias_keys.difference(&non_rep).cloned().collect();
                if !missing_keys.is_empty() || !extra_keys.is_empty() {
                    if !missing_keys.is_empty() {
                        errors.push(format!(
                            "aliases missing keys for all non-representatives: {:?}",
                            missing_keys
                        ));
                    }
                    if !extra_keys.is_empty() {
                        errors.push(format!(
                            "aliases contain extra keys that should be representatives (or not candidates): {:?}",
                            extra_keys
                        ));
                    }
                }

                // 3c) Each alias value must be one of the representatives, and key != value
                for (k, v) in aliases.iter() {
                    if !reps_set.contains(v) {
                        errors.push(format!(
                            "alias value for key \"{k}\" must be a member of representatives; got \"{v}\""
                        ));
                    }
                    if k == v {
                        errors.push(format!(
                            "alias key and value must not be equal; got \"{k}\""
                        ));
                    }
                }

                // 3d) Special check for "yes" and "no"
                if aliases.get("yes").map(|s| s.as_str()) == Some("no") {
                    errors.push(r#""yes" must not map to "no""#.to_string());
                }
                if aliases.get("no").map(|s| s.as_str()) == Some("yes") {
                    errors.push(r#""no" must not map to "yes""#.to_string());
                }
            }
        }

        // 4) Exact partition check: representatives ∪ alias_keys == candidates and disjointness implied
        if let Some(aliases) = self.aliases.as_ref() {
            let union: HashSet<String> = reps_set
                .union(&aliases.keys().cloned().collect())
                .cloned()
                .collect();
            if union != candidates {
                // Report symmetric difference for clarity
                let mut missing_from_union: Vec<String> =
                    candidates.difference(&union).cloned().collect();
                let mut not_in_candidates: Vec<String> =
                    union.difference(&candidates).cloned().collect();
                missing_from_union.sort();
                not_in_candidates.sort();
                if !missing_from_union.is_empty() {
                    errors.push(format!(
                        "partition error: some candidates are neither representatives nor alias keys: {:?}",
                        missing_from_union
                    ));
                }
                if !not_in_candidates.is_empty() {
                    errors.push(format!(
                        "partition error: representatives or alias keys include items not in candidates: {:?}",
                        not_in_candidates
                    ));
                }
            }
        } else {
            // If aliases are None, then all candidates must be representatives
            if reps_set != candidates {
                let mut missing: Vec<String> = candidates.difference(&reps_set).cloned().collect();
                missing.sort();
                errors.push(format!(
                    "when aliases is null, representatives must cover all candidates; missing: {:?}",
                    missing
                ));
            }
        }

        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }

    fn normalize(&mut self) {
        self.representatives.sort();
    }
}

// ----- Static schema and prompt (reuse the previous prompt verbatim) -----

fn schema_text() -> &'static str {
    r#"{
  "type": "object",
  "required": [
    "representatives",
    "aliases",
    "enabled_by_default",
    "option_name"
  ],
  "properties": {
    "representatives": {
      "type": "array",
      "items": { "type": "string" },
      "uniqueItems": true,
      "default": []
    },
    "aliases": { "type": ["object", "null"] },
    "enabled_by_default": { "type": ["boolean", "null"] },
    "option_name": { "type": "string" }
  },
  "additionalProperties": false
}"#
}

fn extraction_prompt() -> String {
    r#"
You will be given Autotools fragments (configure.ac/configure shell, m4 macros, Makefile.am snippets, and related variable logic). For each build option, extract only the minimal facts below and return JSON conforming exactly to the schema. Output JSON only.

Definitions:
- 'State': a set of option values that yield the same externally visible effects (defines, flags, libs, subdirs, config files).
- 'Candidates': All non-empty, non-arbitrary literals that can be passed as values of the build option.

Extraction procedure:
1. Candidates := the input field "candidates". Do not infer new literals beyond this list.
2. For each candidate literal, determine external effects and partition candidates into states (identical effects = same state).
3. For each state, pick exactly one representative from Candidates and add it to "representatives", and add rest non-representative candidates to the Keys of "aliases".
  - "representatives" + "aliases keys" = "candidates".
  - You must not choose "auto"/"detect"/similar as representatives since they are highly likely to have the same state as either of the boolean values in the end.
4. Construct "aliases" from the partition:
  a. Keys are all non-representative members of each state.
     - Formally, "alias keys" = "values" − "representatives".
  b. For each such member m, set aliases[m] to representative(state).
  c. For any alias, mapped value ∈ "representatives"
  d. For "yes" and "no", you must not map one of them to the other (e.g. "yes": "no" is prohibited).
5. Determine enabled_by_default by the following precedence:
  a. Help text: (on)/(off) or [default=yes]/[default=no].
  b. The IF-NOT-SET default in AC_ARG_*.
  c. Later shell logic setting a default (e.g. : ${enable_foo=no}).
  d. If option is non-binary (auto/enums) and no binary default is forced, use null.
  e. Otherwise null.

Per-option output fields:
1. option_name: copy the given name.
2. representatives: one representative literal per distinct state. Do not include aliases that normalize to another value.
3. aliases: mapping constructed under the rules above.
4. enabled_by_default: true/false/null as determined by rules above.

Normalization rules:
- Include enums like 'foo', 'bar'.
- Parenthetical (on)/(off) in help is authoritative.

Input format:
{ "name": "...", "declaration": "...", "fragments": ["...", "..."], "candidates": ["...", "..."] }

Strictness:
- Return exactly one top-level, minified JSON object.
- No comments or extra keys.
- Output must validate against the schema.
"#.to_string()
}

const MODEL: &str = "gpt-5-nano";

/// Package the schema + prompt + user fragments into one user message.
fn compose_user_content(
    name: String,
    declaration: String,
    fragments: &[String],
    candidates: &[String],
) -> String {
    serde_json::json!({
        "schema": serde_json::from_str::<serde_json::Value>(schema_text()).unwrap(),
        "instruction": extraction_prompt(),
        "input": { "name": name, "declaration": declaration, "fragments": fragments, "candidates": candidates }
    })
    .to_string()
}

fn compose_user_content_with_feedback(
    option_name: String,
    declaration: String,
    contexts: &[String],
    candidates: &[String],
    prev_json: Option<&str>,
    errors: Option<&[String]>,
) -> String {
    let base = compose_user_content(option_name, declaration, contexts, candidates);

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
    build_option: &BuildOption,
) -> Result<BuildOptionLLMAnalysisResult, String> {
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
            .model(MODEL)
            .stream(false)
            .build()
            .map_err(|e| format!("Failed to build LLM client: {}", e))?;

        // Add validation feedback and previous invalid JSON if available
        let prompt = compose_user_content_with_feedback(
            build_option.option_name.clone(),
            build_option.declaration.clone(),
            &build_option.context,
            &build_option.candidates,
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

                match serde_json::from_str::<BuildOptionLLMAnalysisResult>(&text) {
                    Ok(mut result) => match result.validate(&build_option.candidates) {
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
                    },
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

/// Analyze various properties of build options using LLMs
pub(super) async fn analyze_build_options<'a, I: Iterator<Item = &'a BuildOption>>(
    build_options: I,
) -> Vec<BuildOptionLLMAnalysisResult> {
    futures::stream::iter(
        build_options.map(|build_option| make_api_request_with_retry(build_option)),
    )
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

fn show_cost(usage: Usage) {
    // Show usage and rough cost estimation

    eprintln!(
        "Usage: prompt={} completion={} total={}",
        usage.prompt_tokens, usage.completion_tokens, usage.total_tokens
    );

    const M: f64 = 1_000_000.;
    // Simple cost estimation (adjust rates to your provider/model)
    let (prompt_rate, completion_rate) = match MODEL {
        // (input, output) USD per 1M token
        "gpt-5" => (1.25, 10.),
        "gpt-5-mini" => (0.25, 2.),
        _ => (0.05, 0.40), // gpt5-nano
    };
    let cost = (usage.prompt_tokens as f64) / M * prompt_rate
        + (usage.completion_tokens as f64) / M * completion_rate;
    eprintln!("Estimated cost: ${:.6}", cost);
}
