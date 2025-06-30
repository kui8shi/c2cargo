use std::{collections::HashMap, hash::Hash};

use super::{
    Analyzer, Arithmetic, AstVisitor, Condition, Guard, GuardBodyPair, M4Macro, Node, NodeId,
    Parameter, PatternBodyPair, Word, WordFragment,
};

use slab::Slab;

#[derive(Debug, Clone, PartialEq, Eq, Ord, Hash)]
pub(crate) struct Location {
    pub node_id: NodeId,
    pub line: usize,
    pub is_left: bool,
}

impl PartialOrd for Location {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some((self.line, self.is_left).cmp(&(other.line, other.is_left)))
    }
}

/// Struct represents various types of variable names used in assignments.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum LValue {
    /// String literal. Direct variable reference.
    Lit(String),
    /// Variable name. Indirect variable reference.
    Var(String, Location),
    /// Dynamically constructed variable name. Indirect variable reference.
    Concat(Vec<LValue>),
}

/// Struct represents various types of values assigned to variables.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum RValue {
    /// String literal. It could be used in lhs or rhs.
    Lit(String),
    /// Variable referenece. It could used in lhs or rhs.
    Var(String, Location),
    /// String literal represented as a concatenation of rvalues
    Concat(Vec<RValue>),
    /// Dynamically constructed variable name.
    /// e.g. \"\$${var1}_${var2}_suffix\" becomes Ref([Var(var1), Lit(_), Var(var2), Lit(_suffix)])
    Ref(Vec<RValue>),
    /// Arbitrary shell commands applied to emit values
    /// (shell_string, depending_variables)
    Shell(String, Vec<RValue>),
}

impl RValue {
    pub(crate) fn vars(&self) -> Option<Vec<(String, Location)>> {
        match self {
            RValue::Lit(_) => None,
            RValue::Var(s, loc) => Some(vec![(s.to_owned(), loc.clone())]),
            RValue::Concat(v) => Some(v.iter().map(|e| e.vars()).flatten().flatten().collect()),
            RValue::Ref(v) => Some(v.iter().map(|e| e.vars()).flatten().flatten().collect()),
            RValue::Shell(_, v) => Some(v.iter().map(|e| e.vars()).flatten().flatten().collect()),
        }
    }
}

impl Into<Option<LValue>> for &RValue {
    fn into(self) -> Option<LValue> {
        match self {
            RValue::Lit(_) => None,
            RValue::Var(name, _loc) => Some(LValue::Lit(name.to_owned())),
            RValue::Ref(rvalues) => Some(LValue::Concat({
                let mut lvalues = Vec::new();
                for rvalue in rvalues {
                    match rvalue {
                        RValue::Lit(lit) => {
                            lvalues.push(LValue::Lit(lit.to_owned()));
                        }
                        RValue::Var(name, loc) => {
                            lvalues.push(LValue::Var(name.to_owned(), loc.clone()));
                        }
                        _ => return None,
                    }
                }
                lvalues
            })),
            _ => None,
        }
    }
}

#[derive(Debug)]
pub(super) struct VariableAnalyzer<'a> {
    nodes: &'a mut Slab<Node>,
    pub guards: HashMap<Location, Vec<Guard>>,
    pub evals: HashMap<LValue, Vec<(Option<RValue>, Location)>>,
    pub defines: HashMap<NodeId, HashMap<String, Vec<Location>>>,
    pub uses: HashMap<NodeId, HashMap<String, Vec<Location>>>,
    conds: Vec<Guard>,
    denied: Option<Guard>,
    cursor: Option<NodeId>,
}

impl<'a> VariableAnalyzer<'a> {
    /// Create a new VariableAnalyzer and visit the given command.
    pub fn new(nodes: &'a mut Slab<Node>) -> Self {
        Self {
            nodes,
            guards: HashMap::new(),
            evals: HashMap::new(),
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
    }

    fn current_location(&self) -> Location {
        Location {
            node_id: self.cursor.unwrap(),
            line: self.get_node(self.cursor.unwrap()).range_start().unwrap(),
            is_left: true,
        }
    }

    fn clear(&mut self) {
        self.defines.clear();
        self.uses.clear();
        self.conds.clear();
    }

    fn record_variable_definition(&mut self, name: &str) {
        let id = self.cursor.unwrap();
        let loc = self.current_location();
        self.defines
            .entry(id)
            .or_default()
            .entry(name.to_owned())
            .or_insert(Vec::new())
            .push(loc.clone());
        self.guards.insert(loc, self.conds.clone());
    }

    fn record_variable_usage(&mut self, name: &str) {
        let id = self.cursor.unwrap();
        let loc = self.current_location();
        self.uses
            .entry(id)
            .or_default()
            .entry(name.to_owned())
            .or_insert(Vec::new())
            .push(loc.clone());
        self.guards.insert(loc, self.conds.clone());
    }

    /// parse a body of eval assignment. It is expected to take `word` as a concatenated word fragments
    /// currently we don't support mixed lhs value (eigther single literal or single variable)
    fn parse_eval_assignment(&self, frags: &[WordFragment<String>]) -> (LValue, Option<RValue>) {
        let mut lhs = Vec::new();
        let mut rhs = Vec::new();
        let mut is_lhs = true;
        let mut is_ref = false;
        let loc = self.current_location();
        for frag in frags.iter() {
            match frag {
                WordFragment::Escaped(s) if s == "\"" => (),
                WordFragment::Escaped(s) if s == "$" => {
                    is_ref = true;
                }
                WordFragment::Param(Parameter::Var(s)) if is_lhs => {
                    lhs.push(LValue::Var(s.to_owned(), loc.clone()));
                }
                WordFragment::Param(Parameter::Var(s)) if !is_lhs => {
                    rhs.push(RValue::Var(s.to_owned(), loc.clone()));
                }
                WordFragment::Literal(s) if is_lhs => {
                    if s.contains("=") {
                        let mut split = s.split("=");
                        if let Some(lit) = split.next() {
                            if !lit.is_empty() {
                                lhs.push(LValue::Lit(lit.to_owned()));
                            }
                        }
                        if let Some(lit) = split.next() {
                            if !lit.is_empty() {
                                rhs.push(RValue::Lit(lit.to_owned()));
                            }
                        }
                        is_lhs = false;
                    } else {
                        lhs.push(LValue::Lit(s.to_owned()));
                    }
                }
                WordFragment::Literal(s) if !is_lhs => {
                    let s = s.strip_prefix("=").unwrap_or(s).to_owned();
                    rhs.push(RValue::Lit(s));
                }
                WordFragment::DoubleQuoted(inner_frags) if !is_lhs => {
                    for inner_frag in inner_frags {
                        match inner_frag {
                            WordFragment::Escaped(s) if s == "$" => {
                                is_ref = true;
                            }
                            WordFragment::Literal(s) => {
                                rhs.push(RValue::Lit(s.to_owned()));
                            }
                            WordFragment::Param(Parameter::Var(s)) => {
                                rhs.push(RValue::Var(s.to_owned(), loc.clone()));
                            }
                            _ => (),
                        }
                    }
                }
                _ => (),
            }
        }
        let lhs = if lhs.len() <= 1 {
            lhs.pop().unwrap()
        } else {
            LValue::Concat(lhs)
        };
        if is_ref {
            rhs = vec![RValue::Ref(rhs)];
        }
        if rhs.len() <= 1 {
            (lhs, rhs.pop())
        } else {
            (lhs, Some(RValue::Concat(rhs)))
        }
    }
}

impl<'a> AstVisitor for VariableAnalyzer<'a> {
    fn get_node(&self, node_id: NodeId) -> &Node {
        &self.nodes[node_id]
    }

    fn visit_top(&mut self, node_id: NodeId) {
        self.cursor.replace(node_id);
        self.walk_node(node_id);
        self.nodes[node_id].defines = self.defines.get(&node_id).cloned().unwrap_or_default();
        self.nodes[node_id].uses = self.uses.get(&node_id).cloned().unwrap_or_default();
    }

    fn visit_node(&mut self, node_id: NodeId) {
        // Save
        let saved_cursor = self.cursor.replace(node_id);
        dbg!(&self.get_node(node_id));
        // Walk
        if !self.get_node(node_id).is_top_node() {
            self.walk_node(node_id);
            // Assign collected variable to the node
            self.nodes[node_id].defines = self.defines.get(&node_id).cloned().unwrap_or_default();
            self.nodes[node_id].uses = self.uses.get(&node_id).cloned().unwrap_or_default();
        }
        // Recover
        self.cursor = saved_cursor;
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

    fn visit_and_or(&mut self, negated: bool, condition: &Condition<String>, cmd: NodeId) {
        self.conds.push(if negated {
            Guard::Not(Box::new(Guard::Cond(condition.clone())))
        } else {
            Guard::Cond(condition.clone())
        });
        self.walk_and_or(negated, condition, cmd);
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

    fn visit_command(&mut self, cmd_words: &[Word<String>]) {
        if let Some(first) = cmd_words.get(0) {
            if is_eval(first) {
                if let Some(Word::Concat(frags)) = cmd_words.get(1) {
                    let (lhs, rhs) = self.parse_eval_assignment(frags);
                    let loc = Location {
                        node_id: self.cursor.unwrap(),
                        line: self.get_node(self.cursor.unwrap()).range_start().unwrap(),
                        is_left: true,
                    };
                    self.evals.entry(lhs).or_default().push((rhs, loc.clone()));
                    self.guards.insert(loc, self.conds.clone());
                }
            }
        }
        self.walk_command(cmd_words);
    }
}

fn is_eval(word: &Word<String>) -> bool {
    match word {
        Word::Single(f) => matches!(f, WordFragment::Literal(t) if t == "eval"),
        Word::Concat(frags) => {
            frags.len() == 1 && matches!(&frags[0], WordFragment::Literal(t) if t == "eval")
        }
        _ => false,
    }
}
