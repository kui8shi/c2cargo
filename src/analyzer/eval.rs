use super::{AstVisitor, Node, NodeId, Parameter, Word, WordFragment};
use slab::Slab;
use std::collections::{HashMap, HashSet};

/// Represents an `eval` invocation that builds dynamic variable references.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EvalMatch {
    /// The assignment word passed to `eval`, e.g. `cclist_chosen="$cclist$abi1"`.
    pub assignment: Word<String>,
    /// The name of the variable being defined (left side of assignment).
    pub var_name: String,
    /// The names of variables referenced dynamically inside the assignment.
    pub ref_names: Vec<String>,
    /// Literal parts extracted from the assignment for structure analysis.
    pub literal_parts: Vec<String>,
}

/// Represents possible r-values (right-hand side values) for a variable
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VariableValue {
    /// Direct string literal value
    Literal(String),
    /// Value from command substitution (not evaluated)
    CommandSubst(String),
    /// Value from another variable (for chaining)
    Variable(String),
    /// Value from user-defined variable (ignored in analysis)
    UserDefined,
    /// Value from list expansion (special case)
    ListItem(String),
}

/// Represents a special operation in the backward taint analysis
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SpecialOperation {
    /// List expansion: variable ← (list) ← source_var
    ListExpansion(String),
    /// Command substitution: variable ← (cmd) ← command
    CommandExpansion(String),
    /// Eval expansion: variable ← (eval) ← [var1, var2, ...]
    EvalExpansion(Vec<String>),
}

/// Results of backward taint analysis for a variable
#[derive(Debug, Clone)]
pub struct TaintAnalysisResult {
    /// Possible r-values for this variable
    pub values: HashSet<VariableValue>,
    /// Variables that this variable depends on
    pub dependencies: HashSet<String>,
    /// Special operations encountered in the chain
    pub operations: Vec<SpecialOperation>,
}

/// Visitor to find `eval` commands generating dynamic variable references.
#[derive(Debug)]
pub struct EvalAnalyzer<'a> {
    nodes: &'a Slab<Node>,
    /// Collected matches of dynamic eval assignments.
    pub matches: Vec<EvalMatch>,
}

impl<'a> EvalAnalyzer<'a> {
    /// Create a new EvalFinder.
    pub fn find_eval_dynamic_refs(nodes: &'a Slab<Node>, top_ids: &[NodeId]) -> Self {
        let mut s = Self {
            nodes,
            matches: Vec::new(),
        };
        for &id in top_ids {
            s.visit_top(id);
        }
        s
    }
}

impl<'a> AstVisitor for EvalAnalyzer<'a> {
    fn get_node(&self, node_id: NodeId) -> &Node {
        &self.nodes[node_id]
    }

    fn visit_command(&mut self, cmd_words: &[Word<String>]) {
        if let Some(first) = cmd_words.get(0) {
            let is_eval = match first {
                Word::Single(f) => matches!(f, WordFragment::Literal(t) if t == "eval"),
                Word::Concat(frags) => {
                    frags.len() == 1 && matches!(&frags[0], WordFragment::Literal(t) if t == "eval")
                }
                _ => false,
            };
            if is_eval {
                dbg!(&cmd_words);
                for assign in &cmd_words[1..] {
                    if let Word::Concat(frags) = assign {
                        if let Some(WordFragment::Literal(left)) = frags.first() {
                            if let Some(var_name) = left.strip_suffix('=') {
                                let mut params = Vec::new();
                                let mut literals = Vec::new();

                                // Collect parameters and literals from all fragments
                                for frag in frags.iter().skip(1) {
                                    match frag {
                                        WordFragment::DoubleQuoted(inner) => {
                                            for inner_frag in inner {
                                                match inner_frag {
                                                    WordFragment::Param(Parameter::Var(n)) => {
                                                        params.push(n.clone());
                                                    }
                                                    WordFragment::Literal(lit) => {
                                                        // Only capture non-empty literal content
                                                        if !lit.is_empty() {
                                                            literals.push(lit.clone());
                                                        }
                                                    }
                                                    _ => {}
                                                }
                                            }
                                        }
                                        WordFragment::Param(Parameter::Var(n)) => {
                                            params.push(n.clone());
                                        }
                                        WordFragment::Literal(lit) => {
                                            // Only capture non-empty literal content
                                            if !lit.is_empty() {
                                                literals.push(lit.clone());
                                            }
                                        }
                                        // Skip escaped quotes and dollar signs - they're syntax, not content
                                        WordFragment::Escaped(esc) if esc == "\"" || esc == "$" => {
                                        }
                                        WordFragment::Escaped(esc) => {
                                            // Keep other escaped content like actual escaped characters
                                            literals.push(esc.clone());
                                        }
                                        _ => {}
                                    }
                                }
                                if params.len() > 1 {
                                    self.matches.push(EvalMatch {
                                        assignment: assign.clone(),
                                        var_name: var_name.to_string(),
                                        ref_names: params,
                                        literal_parts: literals,
                                    });
                                }
                            }
                        }
                    }
                }
            }
        }
        self.walk_command(cmd_words);
    }
}
