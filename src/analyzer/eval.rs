use super::{AstVisitor, TopLevelWord};
use autoconf_parser::ast::{
    minimal::{Command, Word, WordFragment},
    Parameter,
};

/// Represents an `eval` invocation that builds dynamic variable references.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EvalMatch {
    /// The assignment word passed to `eval`, e.g. `cclist_chosen="$cclist$abi1"`.
    pub assignment: TopLevelWord,
    /// The names of variables referenced dynamically inside the assignment.
    pub ref_names: Vec<String>,
}

/// Visitor to find `eval` commands generating dynamic variable references.
#[derive(Debug)]
pub struct EvalAnalyzer {
    /// Collected matches of dynamic eval assignments.
    pub matches: Vec<EvalMatch>,
}

impl EvalAnalyzer {
    /// Create a new EvalFinder.
    pub fn new() -> Self {
        Self {
            matches: Vec::new(),
        }
    }
}

impl AstVisitor for EvalAnalyzer {
    fn visit_command(&mut self, cmd: &Command<String>) {
        if let Command::Cmd(words) = cmd {
            if let Some(first) = words.get(0) {
                let is_eval = match first {
                    Word::Single(f) => matches!(f, WordFragment::Literal(t) if t == "eval"),
                    Word::Concat(frags) => {
                        frags.len() == 1
                            && matches!(&frags[0], WordFragment::Literal(t) if t == "eval")
                    }
                    _ => false,
                };
                if is_eval {
                    for assign in &words[1..] {
                        if let Word::Concat(frags) = assign {
                            if let Some(WordFragment::Literal(left)) = frags.first() {
                                if let Some(_var_name) = left.strip_suffix('=') {
                                    let mut params = Vec::new();
                                    for frag in frags.iter().skip(1) {
                                        if let WordFragment::DoubleQuoted(inner) = frag {
                                            for inner_frag in inner {
                                                if let WordFragment::Param(Parameter::Var(n)) =
                                                    inner_frag
                                                {
                                                    params.push(n.clone());
                                                }
                                            }
                                        }
                                    }
                                    if params.len() > 1 {
                                        self.matches.push(EvalMatch {
                                            assignment: assign.clone(),
                                            ref_names: params,
                                        });
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        self.walk_command(cmd);
    }
}
