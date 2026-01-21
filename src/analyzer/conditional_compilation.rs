use super::Analyzer;
use regex::Regex;
use serde::{Deserialize, Serialize};
use std::{
    collections::{HashMap, HashSet},
    ops::Range,
    path::PathBuf,
};

#[derive(Debug)]
enum ACSubstVarToCPPSymbol {
    /// The expected case:
    /// #if @VAR@
    ///     #define SYMBOL
    /// #endif
    Condition(String, String),
    /// The expected case:
    /// #define SYMBOL @VAR@
    Subst(String, String),
}

#[derive(Debug, Default, Clone, Deserialize, Serialize)]
pub(super) struct ConditionalCompilationMap {
    pub cpp_map: HashMap<String, CCMigraionPolicy>,
    pub subst_to_cpp_map: HashMap<String, CCMigraionPolicy>,
    pub src_incl_map: HashMap<PathBuf, Vec<SourceInclusionCondition>>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub(super) struct SourceInclusionCondition {
    pub negated: bool,
    pub cfg_key: String,
    #[serde(skip_serializing)]
    pub am_conditional_name: String,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub(super) struct CCMigraionPolicy {
    #[serde(rename = "type")]
    pub mig_type: CCMigrationType,
    pub key: Option<String>,
    pub value: Option<String>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(rename_all = "lowercase")]
pub(super) enum CCMigrationType {
    Cfg,
    Env,
    Fixed,
    Set,
    Unset,
}

impl Analyzer {
    pub(crate) fn print_conditional_compilation_map(&self) -> String {
        serde_json::to_string_pretty(self.conditional_compilation_map.as_ref().unwrap()).unwrap()
    }

    pub(super) fn query_conditional_compilation_migration_policy(
        &self,
        key: &str,
    ) -> Option<&CCMigraionPolicy> {
        let symbol = self.may_prefix_cpp_symbol(key);
        let ccm = self.conditional_compilation_map.as_ref().unwrap();
        ccm.cpp_map
            .get(&symbol)
            .or(ccm.subst_to_cpp_map.get(&symbol))
    }

    pub(super) fn create_conditional_compilation_map(&mut self) {
        let cpp_defs = self
            .cpp_defs
            .clone()
            .unwrap()
            .into_iter()
            .filter(|symbol| {
                self.get_project_source_contents()
                    .iter()
                    .any(|c| c.contains(symbol))
            })
            .collect::<HashSet<_>>();
        let fixed_cpp_values = self
            .side_effects_of_frozen_macros
            .as_ref()
            .unwrap()
            .values()
            .flat_map(|effects| effects.cpps.iter())
            .collect::<HashMap<_, _>>();

        let mut cpp_map = HashMap::default();
        for symbol in cpp_defs {
            assert!(!symbol.is_empty());
            let symbol_may_prefixed = self.may_prefix_cpp_symbol(&symbol);
            let cc_entry = if let Some(fixed) = fixed_cpp_values.get(&symbol_may_prefixed) {
                if let Some(value) = fixed {
                    if value == "1" {
                        CCMigraionPolicy {
                            mig_type: CCMigrationType::Set,
                            key: None,
                            value: None,
                        }
                    } else {
                        CCMigraionPolicy {
                            mig_type: CCMigrationType::Fixed,
                            key: None,
                            value: Some(value.clone()),
                        }
                    }
                } else {
                    CCMigraionPolicy {
                        mig_type: CCMigrationType::Unset,
                        key: None,
                        value: None,
                    }
                }
            } else {
                let contents = self
                    .get_project_source_contents()
                    .into_iter()
                    .chain(self.get_project_other_contents().into_iter())
                    .collect::<Vec<_>>();
                if detect_value_usage(&symbol_may_prefixed, &contents) {
                    CCMigraionPolicy {
                        mig_type: CCMigrationType::Env,
                        key: Some(symbol.clone()),
                        value: None,
                    }
                } else {
                    CCMigraionPolicy {
                        mig_type: CCMigrationType::Cfg,
                        key: Some(symbol.to_lowercase()),
                        value: None,
                    }
                }
            };
            cpp_map.insert(symbol_may_prefixed, cc_entry);
        }
        let mut subst_to_cpp_map = HashMap::new();
        for file in self.project_info.subst_files.iter().map(|(_, src)| src) {
            let path = self.project_info.project_dir.join(file);
            let bytes = std::fs::read(path.as_path()).unwrap();
            let content = String::from_utf8_lossy(&bytes);
            for res in parse_ac_subst_header(&content, &self.get_project_source_contents()) {
                match res {
                    ACSubstVarToCPPSymbol::Condition(subst, symbol) => {
                        let policy = CCMigraionPolicy {
                            mig_type: CCMigrationType::Cfg,
                            key: Some(symbol.to_lowercase()),
                            value: None,
                        };
                        subst_to_cpp_map.insert(subst, policy);
                    }
                    ACSubstVarToCPPSymbol::Subst(subst, symbol) => {
                        let policy = CCMigraionPolicy {
                            mig_type: CCMigrationType::Env,
                            key: Some(symbol),
                            value: None,
                        };
                        subst_to_cpp_map.insert(subst, policy);
                    }
                };
            }
        }
        let mut src_incl_map = HashMap::new();
        for file in self.project_info.c_files.iter() {
            if file.am_cond.len() > 0 {
                let conditionals = file
                    .am_cond
                    .iter()
                    .map(|c| SourceInclusionCondition {
                        negated: c.negated,
                        cfg_key: c.var.to_lowercase(),
                        am_conditional_name: c.var.clone(),
                    })
                    .collect::<Vec<_>>();
                src_incl_map.insert(file.value.clone(), conditionals);
            }
        }
        let ccm = ConditionalCompilationMap {
            cpp_map,
            subst_to_cpp_map,
            src_incl_map,
        };
        self.conditional_compilation_map.replace(ccm);
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
                symbol.to_owned()
                // panic!("Invalid CPP symbol: {:?} found", symbol);
            }
        } else {
            symbol.to_owned()
        }
    }
}

/// Detects if a C/C++ symbol is used as a non-boolean value (e.g., in assignments, math).
/// Handles macro aliasing recursively and ignores trivial boolean checks (e.g., `if (SYMBOL)`).
fn detect_value_usage(target_symbol: &str, contents: &[&str]) -> bool {
    let mut visited_symbols = HashSet::new();
    check_usage_recursive(target_symbol, contents, &mut visited_symbols)
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
                    if symbol_re.is_match(macro_value)
                        && check_usage_recursive(macro_name, contents, visited)
                    {
                        return true;
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

fn parse_ac_subst_header(
    subst_header: &str,
    source_contents: &[&str],
) -> Vec<ACSubstVarToCPPSymbol> {
    let mut results = Vec::new();
    let mut processed_ranges: Vec<Range<usize>> = Vec::new();

    // Regex for block: #if @COND@ ... #endif
    let block_re = Regex::new(r"(?ms)^#if\s+@(?<cond>[A-Z0-9_]+)@(?<block>.*?)#endif").unwrap();

    // Regex for define: #define LHS [RHS]
    // Note: rhs captures everything until end of line/comment
    let define_re =
        Regex::new(r"(?m)^\s*#define[ \t]+(?<lhs>[A-Z0-9_]+)(?:[ \t]+(?<rhs>[^\r\n]+))?\s*$")
            .unwrap();

    // 1. Process Conditional Blocks
    for cap in block_re.captures_iter(subst_header) {
        let cond = cap.name("cond").unwrap().as_str().to_string();
        let block_content = cap.name("block").unwrap().as_str();
        let match_range = cap.get(0).unwrap().range();

        processed_ranges.push(match_range);

        for inner_cap in define_re.captures_iter(block_content) {
            if let Some((symbol_name, may_subst_value)) = create_entry(inner_cap) {
                match may_subst_value {
                    None => {
                        results.push(ACSubstVarToCPPSymbol::Condition(cond.clone(), symbol_name));
                    }
                    Some(_) if !detect_value_usage(&symbol_name, source_contents) => {
                        results.push(ACSubstVarToCPPSymbol::Condition(cond.clone(), symbol_name));
                    }
                    _ => (),
                }
            }
        }
    }

    // 2. Process Global definitions
    for cap in define_re.captures_iter(subst_header) {
        let match_start = cap.get(0).unwrap().start();

        if processed_ranges.iter().any(|r| r.contains(&match_start)) {
            continue;
        }

        if let Some((symbol_name, may_subst_value)) = create_entry(cap) {
            match may_subst_value {
                Some(subst_value) => {
                    if detect_value_usage(&symbol_name, source_contents) {
                        results.push(ACSubstVarToCPPSymbol::Subst(subst_value, symbol_name));
                    } else if source_contents.iter().any(|src| src.contains(&symbol_name)) {
                        results.push(ACSubstVarToCPPSymbol::Condition(subst_value, symbol_name));
                    }
                }
                _ => (),
            }
        }
    }

    results
}

fn create_entry(cap: regex::Captures) -> Option<(String, Option<String>)> {
    let lhs = cap.name("lhs").unwrap().as_str().to_string();
    let raw_rhs = cap.name("rhs").map(|m| m.as_str().trim());

    let rhs = match raw_rhs {
        Some(s) if !s.is_empty() => {
            // Clean comments
            let comment_re = Regex::new(r"/\*.*?\*/").unwrap();
            let clean_s = comment_re.replace_all(s, "").trim().to_string();

            if clean_s.is_empty() {
                None
            } else if let Some(subst) = parse_substitution(&clean_s) {
                // Priority Check: If it looks like a substitution (quoted or not), it is subst var
                Some(subst)
            } else if is_literal(&clean_s) {
                // Only if not a substitution, check if it is a literal
                None
            } else {
                // Complex -> Ignore
                return None;
            }
        }
        _ => None,
    };

    Some((lhs, rhs))
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
