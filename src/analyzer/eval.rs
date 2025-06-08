use super::{AstVisitor, Parameter, Word, WordFragment, Node, NodeId};
use slab::Slab;

/// Represents an `eval` invocation that builds dynamic variable references.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EvalMatch {
    /// The assignment word passed to `eval`, e.g. `cclist_chosen="$cclist$abi1"`.
    pub assignment: Word<String>,
    /// The names of variables referenced dynamically inside the assignment.
    pub ref_names: Vec<String>,
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
                for assign in &cmd_words[1..] {
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
        self.walk_command(cmd_words);
    }
}
