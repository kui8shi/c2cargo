use super::{AcWord, Analyzer, Location, ValueExpr};
use crate::analyzer::M4Macro;

pub(super) fn eval_word_macro(
    analyzer: &Analyzer,
    macro_call: &M4Macro,
    loc: &Location,
    internal_field_separator: Option<char>,
) -> Option<Vec<ValueExpr>> {
    match macro_call.name.as_str() {
        "AS_TR_SH" => Some(eval_as_tr_sh(
            analyzer,
            macro_call,
            loc,
            internal_field_separator,
        )),
        _ => None,
    }
}

fn eval_as_tr_sh(
    analyzer: &Analyzer,
    macro_call: &M4Macro,
    loc: &Location,
    internal_field_separator: Option<char>,
) -> Vec<ValueExpr> {
    macro_word_arg_values(analyzer, macro_call, 0, loc, internal_field_separator)
        .into_iter()
        .map(|expr| match expr {
            ValueExpr::Lit(lit) => ValueExpr::Lit(as_tr_sh(&lit)),
            other => other,
        })
        .collect()
}

fn macro_word_arg_values(
    analyzer: &Analyzer,
    macro_call: &M4Macro,
    index: usize,
    loc: &Location,
    internal_field_separator: Option<char>,
) -> Vec<ValueExpr> {
    if let Some(lit) = macro_call.get_arg_as_literal(index) {
        vec![ValueExpr::Lit(lit)]
    } else if let Some(word) = macro_call.get_arg_as_word(index) {
        analyzer.vsa_inspect_word(&word, loc.clone(), internal_field_separator)
    } else if let Some(array) = macro_call.get_arg_as_array(index) {
        array
            .into_iter()
            .flat_map(|word: AcWord| {
                analyzer.vsa_inspect_word(&word, loc.clone(), internal_field_separator)
            })
            .collect()
    } else {
        vec![ValueExpr::Lit(format!("{}(...)", macro_call.name))]
    }
}

fn as_tr_sh(input: &str) -> String {
    let input = input.strip_prefix('$').unwrap_or(input);
    let mut out = String::with_capacity(input.len() + 1);
    for ch in input.chars() {
        if ch.is_ascii_alphanumeric() || ch == '_' {
            out.push(ch);
        } else {
            out.push('_');
        }
    }
    if out
        .chars()
        .next()
        .is_some_and(|ch| ch.is_ascii_digit())
    {
        out.insert(0, '_');
    }
    out
}

#[cfg(test)]
mod tests {
    use super::as_tr_sh;

    #[test]
    fn as_tr_sh_strips_shell_parameter_prefix() {
        assert_eq!(as_tr_sh("$feature_name"), "feature_name");
    }

    #[test]
    fn as_tr_sh_rewrites_non_identifier_characters() {
        assert_eq!(as_tr_sh("feature-name/value"), "feature_name_value");
    }

    #[test]
    fn as_tr_sh_avoids_leading_digits() {
        assert_eq!(as_tr_sh("1.2.3"), "_1_2_3");
    }
}
