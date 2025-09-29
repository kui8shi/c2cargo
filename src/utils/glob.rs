//! Utility module for glob operations

#[derive(Debug)]
pub enum GlobError {
    AsteriskNotAllowed,
    UnterminatedClass,
    EmptyClass,
    InvalidEscape,
    TooManyCombinations(u128, u128),
    AsteriskInEnumeration,
}

impl std::fmt::Display for GlobError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            GlobError::AsteriskNotAllowed => write!(f, "asterisk '*' is not allowed in this glob"),
            GlobError::UnterminatedClass => write!(f, "unterminated character class"),
            GlobError::EmptyClass => write!(f, "empty character class"),
            GlobError::InvalidEscape => write!(f, "invalid escape sequence"),
            GlobError::TooManyCombinations(total, max) => {
                write!(f, "too many combinations: {total} > max {max}")
            }
            GlobError::AsteriskInEnumeration => {
                write!(f, "cannot enumerate patterns containing asterisk '*'")
            }
        }
    }
}

impl std::error::Error for GlobError {}

#[derive(Clone, Debug)]
enum GlobNode {
    Literal(String),      // sequence of literal chars
    AnyChar,              // '?'
    CharClass(Vec<char>), // explicit set (already resolved incl. ranges/negation)
    Asterisk,             // '*' - matches zero or more characters
}

#[derive(Clone, Debug)]
struct GlobAst(Vec<GlobNode>);

/// Enumerate all strings matching the AST.
/// Asterisk is not supported.
pub(crate) fn glob_enumerate(pattern: &str) -> Vec<String> {
    if let Ok(ast) = parse_glob(pattern) {
        let wc = ascii_printable();
        if let Ok(vals) = enumerate(&ast, &wc, 200) {
            return vals;
        }
    }
    Vec::new()
}

/// Check if a string matches a glob pattern (without '*').
/// Supports: literals, '?', '[...]' (ranges, escapes, [!...] / [^...]).
pub(crate) fn glob_match(pattern: &str, text: &str) -> bool {
    let Ok(ast) = parse_glob(pattern) else {
        return false;
    };

    match_ast(&ast, text)
}

/// Parse a glob into AST.
/// Supports: literals, '?', '[...]' (ranges, escapes, [!...] / [^...]), '*'.
/// Backslash works as escape both outside and inside classes.
fn parse_glob(pattern: &str) -> Result<GlobAst, GlobError> {
    let mut it = pattern.chars().peekable();
    let mut nodes = Vec::<GlobNode>::new();
    let mut lit_buf = String::new();

    fn flush_lit(buf: &mut String, nodes: &mut Vec<GlobNode>) {
        if !buf.is_empty() {
            nodes.push(GlobNode::Literal(std::mem::take(buf)));
        }
    }

    while let Some(c) = it.next() {
        match c {
            '*' => {
                flush_lit(&mut lit_buf, &mut nodes);
                nodes.push(GlobNode::Asterisk);
            }
            '?' => {
                flush_lit(&mut lit_buf, &mut nodes);
                nodes.push(GlobNode::AnyChar);
            }
            '\\' => {
                // Escape outside class: take next char as literal
                let Some(n) = it.next() else {
                    return Err(GlobError::InvalidEscape);
                };
                lit_buf.push(n);
            }
            '[' => {
                flush_lit(&mut lit_buf, &mut nodes);
                // parse char class
                let mut negate = false;
                let mut first = true;
                let mut elems: Vec<char> = Vec::new();

                // Special-case: leading '!' or '^' means negation
                if let Some(&nc) = it.peek() {
                    if nc == '!' || nc == '^' {
                        negate = true;
                        it.next();
                    }
                }

                // Collect until ']'
                let mut class_chars: Vec<char> = Vec::new();
                let mut closed = false;
                while let Some(ch) = it.next() {
                    if ch == ']' && !first {
                        closed = true;
                        break;
                    }
                    first = false;
                    if ch == '\\' {
                        // escape inside class
                        let Some(nc) = it.next() else {
                            return Err(GlobError::InvalidEscape);
                        };
                        class_chars.push(nc);
                    } else {
                        class_chars.push(ch);
                    }
                }
                if !closed {
                    return Err(GlobError::UnterminatedClass);
                }
                if class_chars.is_empty() {
                    return Err(GlobError::EmptyClass);
                }

                // Expand ranges a-b inside class_chars
                let mut i = 0;
                while i < class_chars.len() {
                    let c1 = class_chars[i];
                    if i + 2 < class_chars.len() && class_chars[i + 1] == '-' {
                        let c2 = class_chars[i + 2];
                        if (c1 as u32) <= (c2 as u32) {
                            for v in (c1 as u32)..=(c2 as u32) {
                                elems.push(char::from_u32(v).unwrap());
                            }
                            i += 3;
                            continue;
                        }
                    }
                    elems.push(c1);
                    i += 1;
                }

                // Dedup to stable set
                elems.sort_unstable();
                elems.dedup();

                if negate {
                    // Complement over ASCII alphabet (0x20-0x7E by default here)
                    // You can change this universe to, e.g., 0x00-0x7F or a custom set.
                    let universe: Vec<char> =
                        (0x20u32..=0x7Eu32).filter_map(char::from_u32).collect();
                    let excl: std::collections::HashSet<char> = elems.iter().copied().collect();
                    let comp: Vec<char> =
                        universe.into_iter().filter(|c| !excl.contains(c)).collect();
                    if comp.is_empty() {
                        return Err(GlobError::EmptyClass);
                    }
                    nodes.push(GlobNode::CharClass(comp));
                } else {
                    if elems.is_empty() {
                        return Err(GlobError::EmptyClass);
                    }
                    nodes.push(GlobNode::CharClass(elems));
                }
            }
            _ => {
                lit_buf.push(c);
            }
        }
    }
    flush_lit(&mut lit_buf, &mut nodes);
    Ok(GlobAst(nodes))
}

/// Compute total combinations (product of choice counts).
fn combinations_count(ast: &GlobAst, wildcard_alphabet_len: u128) -> u128 {
    ast.0.iter().fold(1u128, |acc, n| {
        let m = match n {
            GlobNode::Literal(s) => {
                if s.is_empty() {
                    1
                } else {
                    1
                }
            }
            GlobNode::AnyChar => wildcard_alphabet_len,
            GlobNode::CharClass(v) => v.len() as u128,
            GlobNode::Asterisk => return u128::MAX, // Signal infinite combinations
        };
        acc.saturating_mul(m)
    })
}

/// Enumerate all strings matching the AST.
/// - `wildcard_alphabet` is used for '?'
/// - `max_combinations` is a safety cap
fn enumerate(
    ast: &GlobAst,
    wildcard_alphabet: &[char],
    max_combinations: u128,
) -> Result<Vec<String>, GlobError> {
    // Check for asterisks first
    if ast.0.iter().any(|node| matches!(node, GlobNode::Asterisk)) {
        // we do not support enumeration of '*'.
        return Err(GlobError::AsteriskInEnumeration);
    }

    let wc_len = wildcard_alphabet.len() as u128;
    let total = combinations_count(ast, wc_len);
    if total > max_combinations {
        return Err(GlobError::TooManyCombinations(total, max_combinations));
    }

    let mut out = Vec::<String>::with_capacity(total.min(1_000_000) as usize);

    fn push_cartesian(
        nodes: &[GlobNode],
        idx: usize,
        cur: &mut String,
        out: &mut Vec<String>,
        wc: &[char],
    ) {
        if idx == nodes.len() {
            out.push(cur.clone());
            return;
        }
        match &nodes[idx] {
            GlobNode::Literal(s) => {
                cur.push_str(s);
                push_cartesian(nodes, idx + 1, cur, out, wc);
                // pop back s.len() chars
                for _ in 0..s.chars().count() {
                    cur.pop();
                }
            }
            GlobNode::AnyChar => {
                for &c in wc {
                    cur.push(c);
                    push_cartesian(nodes, idx + 1, cur, out, wc);
                    cur.pop();
                }
            }
            GlobNode::CharClass(v) => {
                for &c in v {
                    cur.push(c);
                    push_cartesian(nodes, idx + 1, cur, out, wc);
                    cur.pop();
                }
            }
            GlobNode::Asterisk => {
                // This should never be reached due to the check at the start of enumerate()
                unreachable!("Asterisk should be caught by enumerate() validation")
            }
        }
    }

    let mut cur = String::new();
    push_cartesian(&ast.0, 0, &mut cur, &mut out, wildcard_alphabet);
    Ok(out)
}

/// Helper: ASCII printable (0x20..=0x7E)
fn ascii_printable() -> Vec<char> {
    (0x20u32..=0x7Eu32).filter_map(char::from_u32).collect()
}

/// Helper: a-z
fn ascii_lowercase() -> Vec<char> {
    ('a'..='z').collect()
}

fn match_ast(ast: &GlobAst, text: &str) -> bool {
    let text_chars: Vec<char> = text.chars().collect();
    match_nodes(&ast.0, &text_chars, 0, 0)
}

fn match_nodes(nodes: &[GlobNode], text_chars: &[char], node_idx: usize, text_idx: usize) -> bool {
    if node_idx == nodes.len() {
        return text_idx == text_chars.len();
    }

    if text_idx > text_chars.len() {
        return false;
    }

    match &nodes[node_idx] {
        GlobNode::Literal(s) => {
            let pattern_chars: Vec<char> = s.chars().collect();
            if text_idx + pattern_chars.len() > text_chars.len() {
                return false;
            }

            for (i, &pattern_char) in pattern_chars.iter().enumerate() {
                if text_chars[text_idx + i] != pattern_char {
                    return false;
                }
            }

            match_nodes(
                nodes,
                text_chars,
                node_idx + 1,
                text_idx + pattern_chars.len(),
            )
        }
        GlobNode::AnyChar => {
            if text_idx >= text_chars.len() {
                return false;
            }
            match_nodes(nodes, text_chars, node_idx + 1, text_idx + 1)
        }
        GlobNode::CharClass(allowed_chars) => {
            if text_idx >= text_chars.len() {
                return false;
            }

            let text_char = text_chars[text_idx];
            if !allowed_chars.contains(&text_char) {
                return false;
            }

            match_nodes(nodes, text_chars, node_idx + 1, text_idx + 1)
        }
        GlobNode::Asterisk => {
            // Try matching 0 characters (skip the asterisk)
            if match_nodes(nodes, text_chars, node_idx + 1, text_idx) {
                return true;
            }

            // Try matching 1 or more characters
            for i in text_idx..text_chars.len() {
                if match_nodes(nodes, text_chars, node_idx + 1, i + 1) {
                    return true;
                }
            }

            false
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_match_glob_literals() {
        assert!(glob_match("hello", "hello"));
        assert!(!glob_match("hello", "world"));
        assert!(!glob_match("hello", "hell"));
        assert!(!glob_match("hello", "helloo"));
    }

    #[test]
    fn test_match_glob_any_char() {
        assert!(glob_match("h?llo", "hello"));
        assert!(glob_match("h?llo", "hallo"));
        assert!(!glob_match("h?llo", "hllo"));
        assert!(!glob_match("h?llo", "helllo"));
        assert!(glob_match("?", "a"));
        assert!(!glob_match("?", ""));
        assert!(!glob_match("?", "ab"));
    }

    #[test]
    fn test_match_glob_char_class() {
        assert!(glob_match("h[ae]llo", "hello"));
        assert!(glob_match("h[ae]llo", "hallo"));
        assert!(!glob_match("h[ae]llo", "hillo"));

        // Range test
        assert!(glob_match("test[0-9]", "test5"));
        assert!(!glob_match("test[0-9]", "testa"));

        // Negation test
        assert!(glob_match("test[!0-9]", "testa"));
        assert!(!glob_match("test[!0-9]", "test5"));
    }

    #[test]
    fn test_match_glob_asterisk() {
        // Basic asterisk tests
        assert!(glob_match("*", ""));
        assert!(glob_match("*", "anything"));
        assert!(glob_match("*", "multiple words"));

        // Asterisk at start
        assert!(glob_match("*world", "hello world"));
        assert!(glob_match("*world", "world"));
        assert!(!glob_match("*world", "hello worlds"));

        // Asterisk at end
        assert!(glob_match("hello*", "hello world"));
        assert!(glob_match("hello*", "hello"));
        assert!(!glob_match("hello*", "hi hello"));

        // Asterisk in middle
        assert!(glob_match("hello*world", "hello beautiful world"));
        assert!(glob_match("hello*world", "helloworld"));
        assert!(!glob_match("hello*world", "hello world!"));

        // Multiple asterisks
        assert!(glob_match("*hello*world*", "say hello beautiful world now"));
        assert!(glob_match("*hello*world*", "hello world"));
        assert!(!glob_match("*hello*world*", "hello beautiful"));
    }

    #[test]
    fn test_match_glob_asterisk_with_literal_suffix() {
        // The specific case mentioned - should fail
        assert!(!glob_match("*-literal", "aaa-literl"));

        // Should succeed
        assert!(glob_match("*-literal", "aaa-literal"));
        assert!(glob_match("*-literal", "-literal"));
        assert!(glob_match("*-literal", "prefix-literal"));

        // More edge cases
        assert!(!glob_match("*-literal", "aaa-litera"));
        assert!(!glob_match("*-literal", "aaa-literall"));
        assert!(!glob_match("*-literal", ""));
    }

    #[test]
    fn test_match_glob_asterisk_with_literal_prefix() {
        assert!(glob_match("literal-*", "literal-suffix"));
        assert!(glob_match("literal-*", "literal-"));
        assert!(!glob_match("literal-*", "literal"));
        assert!(!glob_match("literal-*", "litera-suffix"));
    }

    #[test]
    fn test_match_glob_complex_patterns() {
        // Combining multiple features
        assert!(glob_match("*.[ch]", "file.c"));
        assert!(glob_match("*.[ch]", "main.h"));
        assert!(!glob_match("*.[ch]", "file.cpp"));

        assert!(glob_match("test?*", "test1file"));
        assert!(glob_match("test?*", "testa"));
        assert!(!glob_match("test?*", "test"));

        // Escaped characters
        assert!(glob_match("test\\*", "test*"));
        assert!(!glob_match("test\\*", "testanything"));

        assert!(glob_match("test\\?", "test?"));
        assert!(!glob_match("test\\?", "testa"));
    }

    #[test]
    fn test_match_glob_edge_cases() {
        // Empty pattern and text
        assert!(glob_match("", ""));
        assert!(!glob_match("", "a"));
        assert!(!glob_match("a", ""));

        // Just asterisk
        assert!(glob_match("*", ""));
        assert!(glob_match("*", "a"));
        assert!(glob_match("*", "anything"));

        // Adjacent asterisks (should be treated as single asterisk)
        assert!(glob_match("**", ""));
        assert!(glob_match("**", "anything"));
        assert!(glob_match("a**b", "ab"));
        assert!(glob_match("a**b", "aXXXb"));
    }

    #[test]
    fn test_match_glob_invalid_patterns() {
        // Invalid patterns should return false
        assert!(!glob_match("[", "a"));
        assert!(!glob_match("[abc", "a"));
        assert!(!glob_match("[]", "a"));
        assert!(!glob_match("test\\", "test"));
    }
}
