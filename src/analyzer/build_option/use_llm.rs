//! LLM analysis module for argument analysis
use serde::{ser::SerializeStruct, Deserialize, Serialize};
use std::collections::HashMap;

use crate::utils::llm_analysis::{LLMAnalysis, LLMAnalysisOutput};

use super::BuildOption;

// ----- Data types for input/output -----

impl Serialize for BuildOption {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut state = serializer.serialize_struct("build_option", 4)?;
        state.serialize_field("name", &self.option_name)?;
        state.serialize_field("declaration", &self.declaration)?;
        state.serialize_field("fragments", &self.context)?;
        state.serialize_field("candidates", &self.value_candidates)?;
        state.end()
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
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

impl LLMAnalysisOutput<Vec<String>> for BuildOptionLLMAnalysisResult {
    /// Validate this result against the prompt-defined rules using the provided `values` as Candidates.
    /// Returns `Ok(())` if valid, or `Err(Vec<String>)` with all detected issues.
    fn validate(&self, values: &Vec<String>) -> Result<(), Vec<String>> {
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
                    r#"If "yes" and "no" are in representatives, they must not hold any other values: {:?}"#,
                    reps_set.iter().filter(|r| !(matches!(r.as_str(), "yes"|"no"))).collect::<Vec<_>>()
                ))
            }
        }

        // 2c) binary representatives must contain yes and no.
        if reps_set.len() <= 2 {
            if !(reps_set.contains("yes") && reps_set.contains("no")) {
                errors.push(format!(
                    r#"Binary representatives must contain yes and no. They must not hold any other values: {:?}"#,
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
}

pub(super) struct LLMUser {}

impl LLMAnalysis for LLMUser {
    type Evidence = Vec<String>;
    type Input = BuildOption;
    type Output = BuildOptionLLMAnalysisResult;

    fn new() -> Self {
        Self {}
    }

    fn schema_text(&self) -> &'static str {
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

    fn instruction_prompt(&self) -> &'static str {
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
"#
    }
}
