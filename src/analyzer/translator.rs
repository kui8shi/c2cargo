use std::collections::HashSet;

use serde::{Deserialize, Serialize};

use crate::utils::llm_analysis::{LLMAnalysis, LLMAnalysisInput, LLMAnalysisOutput};

use super::Analyzer;

impl Analyzer {
    /// Analyze commands and build the dependency graph
    pub fn translate(&mut self) {
        println!("=== TRANSLATE DEBUG: Starting translation analysis ===");

        self.construct_chunks(Some(5), true);
        println!("Constructed {} chunks", self.chunks.len());

        let mut exported = HashSet::new();
        // First, collect I/O for all chunks
        for (i, chunk) in self.chunks.iter() {
            exported.extend(chunk.exported.clone());
            println!(
                "Chunk {}: {} commands, imports {:?}, exports {:?}",
                i,
                chunk.nodes.len(),
                chunk.imported,
                chunk.exported
            );
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(super) struct TranslationInput {
    script: String,
    signature: String,
}

impl LLMAnalysisInput<()> for TranslationInput {
    fn get_evidence_for_validation(&self) -> &() {
        &()
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(super) struct TranslationOutput {
    rust_func_body: String,
}

impl LLMAnalysisOutput<()> for TranslationOutput {
    /// Validate this result against the prompt-defined rules using the provided `values` as Candidates.
    /// Returns `Ok(())` if valid, or `Err(Vec<String>)` with all detected issues.
    fn validate(&self, values: &()) -> Result<(), Vec<String>> {
        Ok(())
    }
}

pub(super) struct LLMUser {}

impl LLMAnalysis for LLMUser {
    type Evidence = ();
    type Input = TranslationInput;
    type Output = TranslationOutput;

    fn new() -> Self {
        Self {}
    }

    fn schema_text(&self) -> &'static str {
        r#"{
  "type": "object",
  "required": [
    "rust_func_body"
  ],
  "properties": {
    "rust_func_body": { "type": "string" }
  },
  "additionalProperties": false
}"#
    }

    fn extraction_prompt(&self) -> &'static str {
        r#"
You are an expert C-to-Rust migration assistant. Your task is to translate Autotools/shell script fragments into equivalent Rust function bodies.

Input format:
{ "script": "...", "signature": "..." }

The "script" contains the original shell/autotools code that needs translation.
The "signature" contains the target Rust function signature that the body should implement.

Translation Guidelines:

1. **Shell Command Translation**:
   - Convert shell commands to appropriate Rust std::process::Command calls
   - Use proper error handling with Result<T, E> return types
   - Replace shell variable expansions with Rust string formatting
   - Convert shell conditionals to Rust if/match statements

2. **Variable Handling**:
   - Convert shell variables to Rust variables with appropriate types
   - Use String for text, bool for flags, Vec<String> for lists
   - Handle environment variables with std::env::var()

3. **File Operations**:
   - Replace shell file tests with std::fs and std::path operations  
   - Use Path::exists(), is_file(), is_dir() instead of [ -f ], [ -d ]
   - Convert file reading/writing to proper Rust I/O

4. **Error Handling**:
   - Always use proper Rust error handling patterns
   - Return Result types for fallible operations
   - Use ? operator for error propagation where appropriate

5. **Dependencies**:
   - Only use standard library unless absolutely necessary
   - If external crates needed, prefer common ones like serde, regex, etc.

6. **Code Style**:
   - Follow Rust naming conventions (snake_case)
   - Add appropriate type annotations
   - Use idiomatic Rust patterns and constructs

Example Translation:
Shell: if [ -f "$CONFIG_FILE" ]; then echo "Found config"; fi
Rust: if std::path::Path::new(&config_file).exists() { println!("Found config"); }

Return only the Rust function body that implements the signature. Do not include the function declaration itself.

Strictness:
- Return exactly one top-level, minified JSON object.
- No comments or extra keys.  
- Output must validate against the schema.
- The rust_func_body should be complete, compilable Rust code.
"#
    }
}
