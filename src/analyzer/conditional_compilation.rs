use super::Analyzer;
use regex::Regex;
use serde::{Deserialize, Serialize};
use std::{
    collections::{HashMap, HashSet},
    ops::Range,
};

#[derive(Debug, PartialEq)]
enum CCVoL {
    /// Matches @VAR_NAME@ or "@VAR_NAME@"
    SubstVar(String),
    /// Matches "string" or 123
    Literal(String),
}

#[derive(Debug)]
struct ACSubstVarToCPPSymbol {
    pub condition: Option<String>,
    pub lhs: String,
    pub rhs: Option<CCVoL>,
}

#[derive(Debug, Default, Clone, Deserialize, Serialize)]
pub(super) struct ConditionalCompilationMap {
    map: HashMap<String, CPPMigraionPolicy>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub(super) struct CPPMigraionPolicy {
    #[serde(rename = "type")]
    pub mig_type: CPPMigrationType,
    pub key: Option<String>,
    pub value: Option<String>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(rename_all = "lowercase")]
pub(super) enum CPPMigrationType {
    Cfg,
    Env,
    Fixed,
    Set,
    Unset,
}

impl Analyzer {
    pub(super) fn query_cpp_migration_policy(&self, key: &str) -> Option<&CPPMigraionPolicy> {
        let symbol = self.may_prefix_cpp_symbol(&key);
        self.conditional_compilation_map
            .as_ref()
            .unwrap()
            .map
            .get(&symbol)
    }

    pub(super) fn create_conditional_compilation_map(&mut self) {
        let mut cpp_defs = self.cpp_defs.clone().unwrap();
        for file in self.project_info.subst_files.iter().map(|(_, src)| src) {
            let path = self.project_info.project_dir.join(file);
            let bytes = std::fs::read(path).unwrap();
            let content = String::from_utf8_lossy(&bytes);
            for res in parse_ac_subst_header(&content) {
                cpp_defs.insert(res.lhs);
            }
        }
        let cpp_defs = cpp_defs
            .into_iter()
            .filter(|symbol| {
                self.get_project_source_contents()
                    .iter()
                    .any(|c| c.contains(symbol))
            })
            .collect::<HashSet<_>>();
        let fixed_cpp_defs = self
            .side_effects_of_frozen_macros
            .as_ref()
            .unwrap()
            .values()
            .map(|effects| effects.cpps.iter())
            .flatten()
            .collect::<HashMap<_, _>>();

        let mut map = ConditionalCompilationMap::default();
        for symbol in cpp_defs {
            assert!(!symbol.is_empty());
            let symbol_may_prefixed = self.may_prefix_cpp_symbol(&symbol);
            let cc_entry = if let Some(fixed) = fixed_cpp_defs.get(&symbol_may_prefixed) {
                if let Some(value) = fixed {
                    if value == "1" {
                        CPPMigraionPolicy {
                            mig_type: CPPMigrationType::Set,
                            key: None,
                            value: None,
                        }
                    } else {
                        CPPMigraionPolicy {
                            mig_type: CPPMigrationType::Fixed,
                            key: None,
                            value: Some(value.clone()),
                        }
                    }
                } else {
                    CPPMigraionPolicy {
                        mig_type: CPPMigrationType::Unset,
                        key: None,
                        value: None,
                    }
                }
            } else if detect_value_usage(&symbol_may_prefixed, &self.get_project_source_contents())
            {
                CPPMigraionPolicy {
                    mig_type: CPPMigrationType::Env,
                    key: Some(symbol.clone()),
                    value: None,
                }
            } else {
                CPPMigraionPolicy {
                    mig_type: CPPMigrationType::Cfg,
                    key: Some(symbol.to_lowercase()),
                    value: None,
                }
            };
            map.map.insert(symbol_may_prefixed, cc_entry);
        }
        self.conditional_compilation_map.replace(map);
    }

    fn may_prefix_cpp_symbol(&self, symbol: &str) -> String {
        if let Some(prefix) = self.cpp_prefix.as_ref() {
            let first_char = symbol.chars().next().unwrap();
            // cf. AX_PREFIX_CONFIG_H
            if first_char.is_ascii_uppercase() || first_char == '_' {
                prefix.to_uppercase() + symbol
            } else if first_char.is_ascii_lowercase() {
                prefix.to_lowercase() + symbol
            } else {
                panic!("Invalid CPP symbol found");
            }
        } else {
            symbol.to_owned()
        }
    }
}

/// Detects if a C/C++ symbol is used as a non-boolean value (e.g., in assignments, math).
/// Handles macro expansions recursively and ignores trivial boolean checks (e.g., `if (SYMBOL)`).
fn detect_value_usage(target_symbol: &str, contents: &[&str]) -> bool {
    let mut visited_symbols = HashSet::new();
    check_usage_recursive(target_symbol, &contents, &mut visited_symbols)
}

fn check_usage_recursive(symbol: &str, contents: &[&str], visited: &mut HashSet<String>) -> bool {
    // Prevent infinite recursion (e.g., circular macros A -> B -> A)
    if !visited.insert(symbol.to_string()) {
        return false;
    }

    // Regex to find the specific symbol (whole word)
    let symbol_pattern = format!(r"\b{}\b", regex::escape(symbol));
    let symbol_re = Regex::new(&symbol_pattern).expect("Invalid symbol regex");

    // Regex to ignore trivial boolean checks: `if (SYMBOL)` or `if (!SYMBOL)`
    let boolean_check_pattern = format!(r"^\s*if\s*\(\s*!?\s*{}\s*\)", regex::escape(symbol));
    let boolean_check_re = Regex::new(&boolean_check_pattern).expect("Invalid boolean regex");

    // Regex to parse #define directives: Captures (1) Macro Name, (2) Value (RHS)
    let define_re =
        Regex::new(r"^\s*#\s*define\s+(\w+)(?:\(.*\))?\s+(.*)").expect("Invalid define regex");

    for content in contents {
        for line in content.lines() {
            // Optimization: Skip lines not containing the symbol
            if !symbol_re.is_match(line) {
                continue;
            }

            let trimmed = line.trim_start();

            // Case 1: Preprocessor Directive (#define)
            if trimmed.starts_with('#') {
                if let Some(caps) = define_re.captures(line) {
                    let macro_name = caps.get(1).map_or("", |m| m.as_str());
                    let macro_value = caps.get(2).map_or("", |m| m.as_str());

                    // If our symbol appears in the RHS, check if the macro itself (LHS) is used as a value.
                    if symbol_re.is_match(macro_value) {
                        if check_usage_recursive(macro_name, contents, visited) {
                            return true;
                        }
                    }
                }
                continue;
            }

            // Case 2: Standard Code Usage
            // If it matches a trivial boolean check, ignore it.
            if boolean_check_re.is_match(line) {
                continue;
            }

            // Otherwise, it's a complex usage (assignment, comparison, function arg, etc.)
            return true;
        }
    }

    false
}

fn parse_ac_subst_header(content: &str) -> Vec<ACSubstVarToCPPSymbol> {
    let mut results = Vec::new();
    let mut processed_ranges: Vec<Range<usize>> = Vec::new();

    // Regex for block: #if @COND@ ... #endif
    let block_re = Regex::new(r"(?ms)^#if\s+@(?<cond>[A-Z0-9_]+)@(?<block>.*?)#endif").unwrap();

    // Regex for define: #define LHS [RHS]
    // Note: rhs captures everything until end of line/comment
    let define_re =
        Regex::new(r"(?m)^\s*#define\s+(?<lhs>[A-Z0-9_]+)(?:\s+(?<rhs>[^\r\n]+))?$").unwrap();

    // 1. Process Conditional Blocks
    for cap in block_re.captures_iter(content) {
        let cond = cap.name("cond").unwrap().as_str().to_string();
        let block_content = cap.name("block").unwrap().as_str();
        let match_range = cap.get(0).unwrap().range();

        processed_ranges.push(match_range);

        for inner_cap in define_re.captures_iter(block_content) {
            if let Some(entry) = create_entry(inner_cap, Some(cond.clone())) {
                results.push(entry);
            }
        }
    }

    // 2. Process Global definitions
    for cap in define_re.captures_iter(content) {
        let match_start = cap.get(0).unwrap().start();

        if processed_ranges.iter().any(|r| r.contains(&match_start)) {
            continue;
        }

        if let Some(entry) = create_entry(cap, None) {
            if entry.condition.is_none() {
                match entry.rhs {
                    Some(CCVoL::Literal(_)) | None => continue,
                    _ => (),
                }
            }
            results.push(entry);
        }
    }

    results
}

fn create_entry(cap: regex::Captures, condition: Option<String>) -> Option<ACSubstVarToCPPSymbol> {
    let lhs = cap.name("lhs").unwrap().as_str().to_string();
    let raw_rhs = cap.name("rhs").map(|m| m.as_str().trim());

    let rhs_parsed = match raw_rhs {
        Some(s) if !s.is_empty() => {
            // Clean comments
            let comment_re = Regex::new(r"/\*.*?\*/").unwrap();
            let clean_s = comment_re.replace_all(s, "").trim().to_string();

            if clean_s.is_empty() {
                None
            } else if let Some(subst) = parse_substitution(&clean_s) {
                // Priority Check: If it looks like a substitution (quoted or not), it is SubstVar
                Some(CCVoL::SubstVar(subst))
            } else if is_literal(&clean_s) {
                // Only if not a substitution, check if it is a literal
                Some(CCVoL::Literal(clean_s))
            } else {
                // Complex -> Ignore
                return None;
            }
        }
        _ => None,
    };

    Some(ACSubstVarToCPPSymbol {
        condition,
        lhs,
        rhs: rhs_parsed,
    })
}

/// Detects @VAR@ OR "@VAR@" and extracts VAR
fn parse_substitution(val: &str) -> Option<String> {
    // Modified Regex:
    // ^ -> Start
    // "? -> Optional opening quote
    // @([A-Z0-9_]+)@ -> The variable pattern
    // "? -> Optional closing quote
    // $ -> End
    let re = Regex::new(r#"^"?@([A-Z0-9_]+)@"?$"#).unwrap();

    // Check if both quotes are present or both absent to be safe?
    // Usually header.in files are well-formed, simple match is enough.
    re.captures(val).map(|c| c[1].to_string())
}

fn is_literal(val: &str) -> bool {
    let is_string = val.starts_with('"') && val.ends_with('"');
    let is_number = val.chars().all(|c| c.is_ascii_digit());
    is_string || is_number
}
