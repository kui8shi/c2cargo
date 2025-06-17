use std::collections::HashMap;

use super::{
    Arithmetic, AstVisitor, Condition, Guard, GuardBodyPair, M4Macro, Node, NodeId, Parameter,
    PatternBodyPair, Word, WordFragment,
};

use slab::Slab;

#[derive(Debug, Clone, PartialEq, Eq, Ord)]
pub(crate) struct VariableLocation {
    pub node_id: NodeId,
    pub line: usize,
    pub is_defined: bool,
}

impl PartialOrd for VariableLocation {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some((self.line, self.is_defined).cmp(&(other.line, other.is_defined)))
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct VariableSpec {
    pub loc: VariableLocation,
    pub guard: Vec<Guard>,
}

#[derive(Debug)]
pub(super) struct VariableAnalyzer<'a> {
    nodes: &'a mut Slab<Node>,
    pub defines: HashMap<String, Vec<VariableSpec>>,
    pub uses: HashMap<String, Vec<VariableSpec>>,
    conds: Vec<Guard>,
    denied: Option<Guard>,
    cursor: Option<NodeId>,
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
            cursor: None,
        }
    }
}

impl<'a> VariableAnalyzer<'a> {
    pub fn analyze(&mut self, node_id: NodeId) {
        self.visit_top(node_id);
        self.conds.clear();
    }

    fn record_variable_definition(&mut self, name: &str) {
        let var_info = VariableSpec {
            loc: VariableLocation {
                node_id: self.cursor.unwrap(),
                line: self.get_node(self.cursor.unwrap()).range_start().unwrap(),
                is_defined: true,
            },
            guard: self.conds.clone(),
        };
        self.defines
            .entry(name.to_owned())
            .or_insert(Vec::new())
            .push(var_info);
    }

    fn record_variable_usage(&mut self, name: &str) {
        let var_info = VariableSpec {
            loc: VariableLocation {
                node_id: self.cursor.unwrap(),
                line: self.get_node(self.cursor.unwrap()).range_start().unwrap(),
                is_defined: false,
            },
            guard: self.conds.clone(),
        };
        self.uses
            .entry(name.to_owned())
            .or_insert(Vec::new())
            .push(var_info);
    }
}

impl<'a> AstVisitor for VariableAnalyzer<'a> {
    fn get_node(&self, node_id: NodeId) -> &Node {
        &self.nodes[node_id]
    }

    fn visit_top(&mut self, node_id: NodeId) {
        let saved = self.cursor.replace(node_id);
        self.walk_node(node_id);
        self.cursor = saved;
    }

    fn visit_node(&mut self, node_id: NodeId) {
        // Save
        let saved_cursor = self.cursor.replace(node_id);
        let saved_defs = self.defines.drain().collect();
        let saved_uses = self.uses.drain().collect();
        // Walk
        if !self.get_node(node_id).is_top_node() {
            self.walk_node(node_id);
        }
        // Assign collected variable to the node
        self.nodes[node_id].defines = self.defines.drain().collect();
        self.nodes[node_id].uses = self.uses.drain().collect();
        // Recover
        self.cursor = saved_cursor;
        self.defines = saved_defs;
        self.defines = saved_uses;
    }

    fn visit_assignment(&mut self, name: &str, word: &Word<String>) {
        self.record_variable_definition(name);
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
        self.record_variable_definition(var);
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
            self.record_variable_usage(name);
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
                self.record_variable_usage(name);
            }
            _ => (),
        }
        self.walk_arithmetic(arith);
    }

    fn visit_parameter(&mut self, param: &Parameter<String>) {
        if let Parameter::Var(name) = param {
            self.record_variable_usage(name);
        }
        self.walk_parameter(param);
    }

    fn visit_m4_macro(&mut self, m4_macro: &M4Macro<String>) {
        if let Some(effects) = &m4_macro.effects {
            if let Some(shell_vars) = &effects.shell_vars {
                for var in shell_vars {
                    if var.is_used() {
                        self.record_variable_usage(&var.name);
                    }
                    if var.is_defined() {
                        self.record_variable_definition(&var.name);
                    }
                }
            }
        }
        self.walk_m4_macro(m4_macro);
    }
}
