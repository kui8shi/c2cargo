use super::Analyzer;
use regex::Regex;
use std::ops::Range;

#[derive(Debug, PartialEq)]
enum CCVoL {
    /// Matches @VAR_NAME@ or "@VAR_NAME@"
    SubstVar(String),
    /// Matches "string" or 123
    Literal(String),
}

#[derive(Debug)]
struct AMSubstToCPP {
    pub condition: Option<String>,
    pub lhs: String,
    pub rhs: Option<CCVoL>,
}

impl Analyzer {
    pub(crate) fn create_conditional_compilation_map(&self) {
        //self.automake().files
        for (src, _) in self
            .project_info
            .subst_files
            .iter()
            .filter(|(_, dst)| dst.extension().is_some_and(|ext| ext == "h" || ext == "c"))
        {
            let content = std::fs::read_to_string(self.project_info.project_dir.join(src)).unwrap();
            dbg!(&src);
            dbg!(&parse_header_in(&content));
        }
    }
}

fn parse_header_in(content: &str) -> Vec<AMSubstToCPP> {
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

fn create_entry(cap: regex::Captures, condition: Option<String>) -> Option<AMSubstToCPP> {
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

    Some(AMSubstToCPP {
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
