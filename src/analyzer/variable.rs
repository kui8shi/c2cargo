use std::collections::HashMap;

use super::{
    Arithmetic, AstVisitor, Condition, Guard, GuardBodyPair, M4Macro, Node, NodeId, Parameter,
    PatternBodyPair, Word, WordFragment,
};

use slab::Slab;

#[derive(Debug)]
pub(super) struct VariableAnalyzer<'a> {
    nodes: &'a mut Slab<Node>,
    pub defines: HashMap<String, Vec<Guard>>,
    pub uses: HashMap<String, Vec<Guard>>,
    conds: Vec<Guard>,
    denied: Option<Guard>,
}

impl<'a> VariableAnalyzer<'a> {
    /// Create a new VariableAnalyzer and visit the given command.
    pub fn new(nodes: &'a mut Slab<Node>) -> Self {
        Self {
            nodes,
            defines: HashMap::new(),
            uses: HashMap::new(),
            conds: Vec::new(),
            denied: None,
        }
    }
}

impl<'a> VariableAnalyzer<'a> {
    pub fn analyze(&mut self, node_id: NodeId) {
        self.clear();

        self.visit_top(node_id);

        // Get defined variables
        self.nodes[node_id].defines = self.defines.clone();

        // Get used variables
        self.nodes[node_id].uses = self.uses.drain().collect();
    }

    fn clear(&mut self) {
        self.defines.clear();
        self.uses.clear();
        self.conds.clear();
    }
}

impl<'a> AstVisitor for VariableAnalyzer<'a> {
    fn get_node(&self, node_id: NodeId) -> &Node {
        &self.nodes[node_id]
    }

    fn visit_assignment(&mut self, name: &str, word: &Word<String>) {
        self.defines.insert(name.to_string(), self.conds.clone());
        self.walk_assignment(name, word);
    }

    fn visit_guard_body_pair(&mut self, pair: &GuardBodyPair<String>) {
        self.conds.push(Guard::Cond(pair.condition.clone()));
        self.walk_guard_body_pair(pair);
        self.denied = self.conds.pop();
    }

    fn visit_if(&mut self, conditionals: &[GuardBodyPair<String>], else_branch: &[NodeId]) {
        for pair in conditionals {
            self.visit_guard_body_pair(pair);
        }
        if !else_branch.is_empty() {
            self.conds
                .push(Guard::Not(Box::new(self.denied.take().unwrap())));
            for c in else_branch {
                self.visit_node(*c);
            }
            self.conds.pop();
        }
    }

    fn visit_for(&mut self, var: &str, words: &[Word<String>], body: &[NodeId]) {
        self.defines.insert(var.to_string(), self.conds.clone());
        self.walk_for(var, words, body);
    }

    fn visit_case(&mut self, word: &Word<String>, arms: &[PatternBodyPair<String>]) {
        self.visit_word(word);
        for arm in arms {
            for w in &arm.patterns {
                self.visit_word(w);
            }
            self.conds
                .push(Guard::Match(word.clone(), arm.patterns.clone()));
            for c in &arm.body {
                self.visit_node(*c);
            }
            self.conds.pop();
        }
    }

    fn visit_chain(&mut self, negated: bool, condition: &Condition<String>, cmd: NodeId) {
        self.conds.push(if negated {
            Guard::Not(Box::new(Guard::Cond(condition.clone())))
        } else {
            Guard::Cond(condition.clone())
        });
        self.walk_chain(negated, condition, cmd);
        self.conds.pop();
    }

    fn visit_word_fragment(&mut self, f: &WordFragment<String>) {
        if let WordFragment::Param(Parameter::Var(name)) = f {
            self.uses.insert(name.clone(), self.conds.clone());
        }
        self.walk_word_fragment(f);
    }

    fn visit_arithmetic(&mut self, arith: &Arithmetic<String>) {
        match arith {
            Arithmetic::Var(name)
            | Arithmetic::PostIncr(name)
            | Arithmetic::PostDecr(name)
            | Arithmetic::PreIncr(name)
            | Arithmetic::PreDecr(name) => {
                self.uses.insert(name.clone(), self.conds.clone());
            }
            _ => (),
        }
        self.walk_arithmetic(arith);
    }

    fn visit_parameter(&mut self, param: &Parameter<String>) {
        if let Parameter::Var(name) = param {
            self.uses
                .entry(name.clone())
                .and_modify(|old_conds| {
                    if old_conds.len() > self.conds.len() {
                        *old_conds = self.conds.clone()
                    }
                })
                .or_insert(self.conds.clone());
        }
        self.walk_parameter(param);
    }

    fn visit_m4_macro(&mut self, m4_macro: &M4Macro<String>) {
        if let Some(effects) = &m4_macro.effects {
            if let Some(shell_vars) = &effects.shell_vars {
                for var in shell_vars {
                    if var.is_used() {
                        self.uses.insert(var.0.clone(), self.conds.clone());
                    }
                    if var.is_defined() {
                        self.defines.insert(var.0.clone(), self.conds.clone());
                    }
                }
            }
        }
        self.walk_m4_macro(m4_macro);
    }
}
