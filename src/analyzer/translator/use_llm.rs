//! LLM analysis module for argument inalysis
use std::{collections::HashMap, io::Write};

use serde::{Deserialize, Serialize};

use crate::utils::llm_analysis::{LLMAnalysis, LLMAnalysisOutput};

use itertools::Itertools;

// ----- Data types for input/output -----

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(super) struct TranslationInput {
    pub id: usize,
    pub script: String,
    pub skeleton: String,
    predefined: String,
}

impl TranslationInput {
    pub fn new(id: usize, script: String, skeleton: String, required_funcs: &[&str]) -> Self {
        Self {
            id,
            script,
            skeleton,
            predefined: get_predefinition(required_funcs),
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(super) struct TranslationOutput {
    pub id: usize,
    pub rust_func_body: String,
    pub rust_func_name: String,
}

fn get_predefinition(required_funcs: &[&str]) -> String {
    let predefinitions = HashMap::from([
        (
            "default_modules",
            "use std::{fs::{self, OpenOptions}, io::Write, path::{Path, PathBuf}};",
        ),
        ("regex", "use regex;"),
        (
            "write_file",
            r#"fn write_file(path: &Path, content: &str) {
  let mut f = OpenOptions::new()
    .create(true)
    .append(true)
    .open(path)
    .expect("file opening");
  writeln!(f, "{content}").expect("writing");
}"#,
        ),
        (
            "define_cfg",
            r#"fn define_cfg(key: &str, value: Option<&str>) {
  println!("cargo:rustc-check-cfg=cfg({})", key);
  if let Some(value) = value {
    println!("cargo:rustc-cfg={}={}", key, value);
  } else {
    println!("cargo:rustc-cfg={}", key);
  }
}"#,
        ),
        (
            "define_env",
            r#"fn define_env(key: &str, value: &str) {
  println!("cargo:rustc-env={}={}", key, value);
}"#,
        ),
    ]);
    std::iter::once("default_modules")
        .chain(required_funcs.iter().cloned())
        .map(|key| predefinitions.get(key).unwrap())
        .join("\n")
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(super) struct TranslationEvidence {
    pub rust_snippets: Vec<String>,
    pub header: String,
    pub footer: String,
}

impl LLMAnalysisOutput<TranslationEvidence> for TranslationOutput {
    /// Validate this result against the prompt-defined rules using the provided `values` as Candidates.
    /// Returns `Ok(())` if valid, or `Err(Vec<String>)` with all detected issues.
    fn validate(&self, evidence: &TranslationEvidence) -> Result<(), Vec<String>> {
        let mut err = Vec::new();
        for rust_snippet in evidence.rust_snippets.iter() {
            if !self.rust_func_body.contains(rust_snippet) {
                err.push(format!(
                    "The translated output must contains a Rust snippet '{}' exactly.",
                    rust_snippet
                ));
            }
        }
        // no-op check
        match detect_no_op_patterns(&self.rust_func_body, &evidence.rust_snippets) {
            Ok(_) => (),
            Err(e) => err.extend(e),
        }
        // compile check
        {
            let rust_func = format!(
                "{}\nfn main() {{}}\nfn {}{}{}{}",
                get_predefinition(&["regex", "write_file"]),
                self.rust_func_name,
                evidence.header,
                self.rust_func_body,
                evidence.footer
            );
            println!("{}", &rust_func);
            let check_dir = std::path::Path::new("/tmp/rust_check");
            let src_dir = check_dir.join("src");

            // Create project directory if it doesn't exist
            std::fs::create_dir_all(&src_dir).unwrap_or_else(|_| {});

            // Create Cargo.toml if it doesn't exist
            let cargo_toml_path = check_dir.join("Cargo.toml");
            if !cargo_toml_path.exists() {
                let cargo_toml = r#"[package]
name = "rust_check"
version = "0.1.0"
edition = "2021"

[dependencies]
regex = "1.0"
"#;
                std::fs::write(&cargo_toml_path, cargo_toml).expect("writing Cargo.toml");
            }

            // Write the code to validate
            let main_rs_path = src_dir.join("main.rs");
            std::fs::write(&main_rs_path, rust_func).expect("writing main.rs");

            // Run cargo check with JSON output
            let output = std::process::Command::new("cargo")
                .arg("check")
                .arg("--message-format=json")
                .current_dir(check_dir)
                .stdout(std::process::Stdio::piped())
                .stderr(std::process::Stdio::piped())
                .output()
                .expect("Executing: cargo check has failed");

            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);

            // Parse JSON messages for errors
            let mut has_errors = false;
            for line in stdout.lines() {
                if let Ok(msg) = serde_json::from_str::<serde_json::Value>(line) {
                    if msg["reason"] == "compiler-message" {
                        if let Some(level) = msg["message"]["level"].as_str() {
                            if level == "error" {
                                has_errors = true;
                                if let Some(text) = msg["message"]["message"].as_str() {
                                    println!("Error: {}", text);
                                    err.push(format!("Compilation error: {}", text));
                                }
                            }
                        }
                    }
                }
            }

            // Also check stderr for non-JSON errors
            if !stderr.is_empty() {
                for line in stderr.lines() {
                    if line.contains("error") {
                        has_errors = true;
                        println!("{}", line.trim());
                        err.push(format!("Compilation error: {}", line.trim()));
                    }
                }
            }

            if !output.status.success() && !has_errors {
                err.push("Compilation failed with unknown error".to_string());
            }
        }
        if err.is_empty() {
            Ok(())
        } else {
            Err(err)
        }
    }
}

fn detect_no_op_patterns(src: &str, values: &Vec<String>) -> Result<(), Vec<String>> {
    let mut err = Vec::new();
    let patterns = [r"let\s+_[A-Za-z0-9_]*\s*=\s*_[A-Za-z0-9_]*".into()]
        .into_iter()
        .chain(
            values
                .iter()
                .map(|val| format!(r"let\s+_[A-Za-z0-9_]*\s*=\s*_?{}", val.replace("{}", ""))),
        );
    for pat in patterns {
        let re = regex::Regex::new(&pat).unwrap();
        for mat in re.find_iter(src) {
            err.push(format!("Evil cheating found: {}.", mat.as_str()));
        }
    }
    if err.is_empty() {
        Ok(())
    } else {
        Err(err)
    }
}

pub(super) struct LLMUser {}

impl LLMAnalysis for LLMUser {
    type Evidence = TranslationEvidence;
    type Input = TranslationInput;
    type Output = TranslationOutput;

    fn new() -> Self {
        Self {}
    }

    fn schema_text(&self) -> &'static str {
        r#"{
  "type": "object",
  "required": [
    "id",
    "rust_func_body",
    "rust_func_name"
  ],
  "properties": {
    "id": { "type": "integer" },
    "rust_func_body": { "type": "string" },
    "rust_func_name": { "type": "string" }
  },
  "additionalProperties": false
}"#
    }

    fn instruction_prompt(&self) -> &'static str {
        r#"You are an expert C-to-Rust migration assistant. Your task is to produce the Rust function body that *exactly* reproduces the semantics and side effects of the given shell/Autotools fragment. Do not summarize, describe, or explain. Only translate and implement.

Input format:
{ "id": ..., "script": "...", "skeleton": "...", "predefined": "..." }

- "id": a unique session number (copy as-is).
- "script": the original shell/Autotools code to translate.
- "skeleton": the Rust function definition template containing `{body}` as placeholder.
- "predefined": predefined rust code that you can utilize the definitions in your output. However, do not include the definitions themselves in your output.

---

### Translation Principles

1. **Behavioral Fidelity (Highest Priority)**
   - Every logical branch, condition, and side effect in the shell script must appear in the Rust code.
   - Always prefer reproducing *behavior* over using all variables syntactically.
   - If a variable is not semantically used in the original logic, do not force dummy references.

2. **Control Flow**
   - Convert `if`, `case`, `for` faithfully to Rust equivalents (`if`, `match`, `for`).
   - Maintain nesting and order of operations exactly.

3. **Variables**
   - Map shell variables to local Rust variables (`String`, `bool`, or `Vec<String>` as appropriate).

4. **Command Execution**
   - Translate shell commands into `std::process::Command` calls.
   - Capture outputs, exit statuses, and stderr as necessary.
   - Simulate redirection (`>`, `2>&1`) via I/O handling.

5. **Filesystem Effects**
   - Map file writes/appends to calls of `write_file`.
   - Handle `cat >`, `echo >>`, and file deletions accurately (`write_file`, `remove_file` etc.).
   - Handle `sed [input-file]`, and file readings accurately (`read_to_string`, etc.).
   - Preserve temporary file lifecycle (`conftest.*` creation and cleanup).

6. **Embedded Rust Snippets**
   - Tokens enclosed in `<rust>...</rust>` are *verbatim Rust expressions* and must appear unquoted.

7. **Output Requirements**
   - Output exactly one minified JSON object:
     - `"id"`: same as input
     - `"rust_func_name"`: concise imperative name (no meta words like “translate” or “chunk”)
     - `"rust_func_body"`: the full Rust function body (no signature, no comments)
   - The code must compile when inserted into the skeleton.
   - No placeholders or dummy `if cfg!(...) {}` branches.

8. **Validation**
   - All file writes, command invocations from the shell must have explicit Rust equivalents.
   - Never invent or skip logic to satisfy formatting rules.
   - Never try to emit a fake or meaningless marker or placeholder just for the parity.

### Example

Shell:
```
if <rust>cfg!(target_os = "windows")</rust> && <rust>cfg!(target_env = "gnu")</rs>; then
echo "include_mpn('x86_64/dos64.m4')" >> ${gmp_tmpconfigm4i}
fi
```

Rust:
```
if cfg!(target_os = "windows") && cfg!(target_env = "gnu") {
let mut f = OpenOptions::new().create(true).append(true).open(&gmp_tmpconfigm4i)?;
writeln!(f, "include_mpn('x86_64/dos64.m4')")?;
}
```

---

### Summary of Strictness
- Always preserve *semantics*.
- Avoid placeholder branches or dummy variable uses.
- Produce deterministic, compilable Rust code faithfully reproducing the Autotools behavior.
"#
    }
}
