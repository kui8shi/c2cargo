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
            "modules",
            "use std::{fs, io::Write, path::{Path, PathBuf}};",
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
    ]);
    std::iter::once("modules")
        .chain(required_funcs.into_iter().cloned())
        .map(|key| predefinitions.get(key).unwrap())
        .join("\n")
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(super) struct TranslationEvidence {
    pub fixed_values: Vec<String>,
    pub header: String,
    pub footer: String,
}

impl LLMAnalysisOutput<TranslationEvidence> for TranslationOutput {
    /// Validate this result against the prompt-defined rules using the provided `values` as Candidates.
    /// Returns `Ok(())` if valid, or `Err(Vec<String>)` with all detected issues.
    fn validate(&self, evidence: &TranslationEvidence) -> Result<(), Vec<String>> {
        let mut err = Vec::new();
        for val in evidence.fixed_values.iter() {
            if !self.rust_func_body.contains(val) {
                err.push(format!(
                    "The translated output must contains a Rust snippet '{}' exactly.",
                    val
                ));
            }
        }
        match detect_no_op_patterns(&self.rust_func_body, &evidence.fixed_values) {
            Ok(_) => (),
            Err(e) => err.extend(e),
        }
        {
            let rust_func = format!(
                "{}\nfn {}{}{}{}",
                get_predefinition(&["regex", "write_file"]),
                self.rust_func_name,
                evidence.header,
                self.rust_func_body,
                evidence.footer
            );
            println!("{}", &rust_func);
            let mut tmp = tempfile::NamedTempFile::new().unwrap();
            writeln!(tmp, "{}", rust_func).expect("writing");
            let output = std::process::Command::new("rustc")
                .arg("--emit=metadata") // compile only metadata, fast
                .arg("-W")
                .arg("unused_variables")
                .arg(tmp.path())
                .stderr(std::process::Stdio::piped())
                .output()
                .expect(&format!("Executing: rustc has failed"));

            let stderr = String::from_utf8_lossy(&output.stderr);
            for line in stderr.lines() {
                if line.contains("error") || line.contains("warning") {
                    println!("{}", line.trim());
                }
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
