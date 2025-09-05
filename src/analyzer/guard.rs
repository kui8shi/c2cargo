use super::{DisplayNode, M4Argument, M4Macro};
use itertools::Itertools;
use slab::Slab;
use std::collections::HashSet;

use super::{
    AcWord, Analyzer, AstVisitor, AutoconfPool, Condition, GuardBodyPair, MayM4, Node, NodeId,
    NodeInfo, Operator, Parameter, ParameterSubstitution, PatternBodyPair, Redirect, Word,
    WordFragment,
};
use crate::analyzer::{as_literal, as_shell, as_var};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum Guard {
    N(bool, Atom), // true if negated
    And(Vec<Self>),
    Or(Vec<Self>),
}

pub(super) type BlockId = usize;

#[derive(Debug, Clone)]
pub(super) struct Block {
    pub block_id: BlockId,
    pub parent: NodeId,
    pub children: Vec<NodeId>,
    pub guards: Vec<Guard>,
}

impl Guard {
    pub(crate) fn confirmed(atom: Atom) -> Guard {
        Guard::N(false, atom)
    }

    pub(crate) fn negated(atom: Atom) -> Guard {
        Guard::N(true, atom)
    }

    pub(crate) fn negate_whole(self) -> Guard {
        match self {
            Guard::N(b, atom) => Guard::N(!b, atom),
            Guard::And(guards) => Guard::Or(guards.into_iter().map(|g| g.negate_whole()).collect()),
            Guard::Or(guards) => Guard::And(guards.into_iter().map(|g| g.negate_whole()).collect()),
        }
    }

    pub(crate) fn make_and(mut guards: Vec<Guard>) -> Guard {
        if guards.len() == 1 {
            guards.pop().unwrap()
        } else {
            Guard::And(guards)
        }
    }

    pub(crate) fn make_or(mut guards: Vec<Guard>) -> Guard {
        if guards.len() == 1 {
            guards.pop().unwrap()
        } else {
            Guard::Or(guards)
        }
    }

    pub(crate) fn has_variable(&self, var_name: &str) -> bool {
        use Atom::*;
        use Guard::*;
        match self {
            N(_, atom) => match atom {
                Var(name, _) => name == var_name,
                Arg(name, _) => name == var_name,
                _ => false,
            },
            And(guards) | Or(guards) => guards.iter().any(|guard| guard.has_variable(var_name)),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Atom {
    ArchGlob(String),         // glob string
    OsAbiGlob(String),        // glob string
    Arch(String),
    Cpu(String),
    Os(String),
    Env(String),
    Abi(String),
    Ext(String), // e.g. sse, neon
    BigEndian,
    HasProgram(String),
    HasLibrary(String),
    HasHeader(String),
    /// "${dir}/filename" -> [Var("dir"), Lit("filename")]
    /// true if absolute
    PathExists(Vec<VoL>, bool),
    Compiler(CompilerCheck),
    Var(String, VarCond),
    Arg(String, VarCond),
    Cmd(NodeId),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VarCond {
    Yes,
    No,
    Empty,
    Unset,
    Set,
    Eq(VoL),
    Lt(VoL),
    Le(VoL),
    Gt(VoL),
    Ge(VoL),
    Match(String), // glob string
    MatchAny,      // *
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VoL {
    Var(String),
    Lit(String),
}

fn as_vol(value: &WordFragment<AcWord>) -> Option<VoL> {
    match value {
        WordFragment::Literal(lit) => Some(VoL::Lit(lit.to_owned())),
        WordFragment::DoubleQuoted(frags) if frags.len() == 1 => as_vol(frags.first().unwrap()),
        WordFragment::Param(Parameter::Var(name)) => Some(VoL::Var(name.to_owned())),
        _ => None,
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CompilerCheck {
    Func(String),
    Symbol { name: String, lib: Option<String> },
    Sizeof(String),
    Attribute(String),
    Link(String),
    Compile(String),
}

/// Compare two conditions.
pub(crate) fn cmp_guards(lhs: &Vec<Guard>, rhs: &Vec<Guard>) -> Option<std::cmp::Ordering> {
    for (l, r) in lhs.iter().rev().zip(rhs.iter().rev()) {
        if l != r {
            // not comparable.
            return None;
        }
    }
    // Here, we know that either condition is a subset of the other.
    // we can decide the order simply by the lengths.
    Some(lhs.len().cmp(&rhs.len()))
}

/// Visitor to find case statements branching given variables.
#[derive(Debug)]
pub(super) struct GuardAnalyzer<'a> {
    pool: &'a mut AutoconfPool<NodeInfo>,
    cursor: Option<NodeId>,
    range: Option<Vec<(usize, usize)>>,
    guard_stack: Vec<Guard>,
    blocks: Slab<Block>,
}

impl Analyzer {
    pub(super) fn blocks_guarded_by_variable(&self, var_name: &str) -> Vec<Block> {
        self.blocks
            .iter()
            .filter_map(|(_, block)| {
                block
                    .guards
                    .last()
                    .is_some_and(|guard| guard.has_variable(var_name))
                    .then_some(block.clone())
            })
            .collect()
    }

    pub(super) fn parent_nodes_of_blocks_guarded_by_variable(&self, var_name: &str) -> Vec<NodeId> {
        let mut children = HashSet::<NodeId>::new();
        let mut ret = Vec::new();
        for block in self.blocks_guarded_by_variable(var_name) {
            children.extend(block.children.iter());
            if !children.contains(&block.parent) {
                if !ret.contains(&block.parent) {
                    ret.push(block.parent)
                }
            }
        }
        ret
    }
}

impl<'a> GuardAnalyzer<'a> {
    pub fn analyze_blocks(pool: &'a mut AutoconfPool<NodeInfo>, top_ids: &[NodeId]) -> Slab<Block> {
        let mut s = Self {
            pool,
            cursor: None,
            range: None,
            guard_stack: Vec::new(),
            blocks: Slab::new(),
        };
        for &id in top_ids {
            s.visit_top(id);
        }
        s.blocks
    }

    fn record_block(&mut self, node_ids: &[NodeId]) {
        let parent = self.cursor.unwrap();
        let new_block_id = self.blocks.insert(Block {
            block_id: 0,
            parent,
            children: node_ids.to_vec(),
            guards: self.guard_stack.clone(),
        });
        self.blocks[new_block_id].block_id = new_block_id;

        // record parent-child relation ships
        for &id in node_ids {
            assert!(self.get_node(parent).range.len() > 0);
            self.pool.nodes[id].info.parent = Some((parent, new_block_id));

            if self.get_node(id).range.is_empty() {
                // propagate ranges information if child doesn't know its range.
                self.pool.nodes[id].range = self.get_node(parent).range.clone();
            }
        }
        self.pool.nodes[parent].info.child_blocks.push(new_block_id);
    }

    fn negate_last_guard(&mut self) {
        let guard = self.guard_stack.pop().unwrap();
        self.guard_stack.push(guard.negate_whole());
    }

    fn equality(&self, a: &AcWord, b: &AcWord) -> Option<Atom> {
        fn interpret_literal(lit: &str) -> VarCond {
            match lit {
                "yes" => VarCond::Yes,
                "no" => VarCond::No,
                "" => VarCond::Empty,
                _ => VarCond::Eq(VoL::Lit(lit.to_owned())),
            }
        }

        fn cancel_x(
            x: &WordFragment<AcWord>,
            var: &WordFragment<AcWord>,
            x_lit: &WordFragment<AcWord>,
        ) -> Option<Atom> {
            if Some("x") == as_literal(x) {
                if let Some(var) = as_var(var) {
                    if let Some(x_lit) = as_literal(x_lit) {
                        if let Some(lit) = x_lit.strip_prefix("x") {
                            return Some(Atom::Var(var.to_owned(), interpret_literal(lit)));
                        }
                    }
                }
            }
            None
        }
        match &a.0 {
            Word::Empty => {
                if let Some(var) = as_shell(b).and_then(as_var) {
                    Some(Atom::Var(var.to_owned(), VarCond::Empty))
                } else {
                    None
                }
            }
            Word::Single(MayM4::Shell(w)) => {
                if let WordFragment::Subst(subst) = w {
                    match &**subst {
                        ParameterSubstitution::Alternative(
                            _,
                            Parameter::Var(name),
                            Some(alter),
                        ) if alter == b => {
                            return Some(Atom::Var(name.to_owned(), VarCond::Set));
                        }
                        ParameterSubstitution::Default(_, Parameter::Var(name), Some(default))
                            if default == b =>
                        {
                            return Some(Atom::Var(name.to_owned(), VarCond::Unset));
                        }
                        ParameterSubstitution::Assign(_, Parameter::Var(name), Some(default))
                            if default == b =>
                        {
                            return Some(Atom::Var(name.to_owned(), VarCond::Unset));
                        }
                        _ => {}
                    }
                } else if let Some(b) = as_shell(b) {
                    if let WordFragment::DoubleQuoted(frags) = w {
                        if frags.len() == 2 {
                            return cancel_x(&frags[0], &frags[1], b);
                        }
                    } else if let Some(var) = as_var(w) {
                        if let Some(lit) = as_literal(b) {
                            return Some(Atom::Var(var.to_owned(), interpret_literal(lit)));
                        } else if let Some(b) = as_vol(b) {
                            return Some(Atom::Var(var.to_owned(), VarCond::Eq(b)));
                        }
                    }
                }
                None
            }
            Word::Concat(concat) if concat.len() == 2 => {
                if let Some(b) = as_shell(b) {
                    if let MayM4::Shell(x) = concat.get(0).unwrap() {
                        if let MayM4::Shell(a) = concat.get(1).unwrap() {
                            return cancel_x(x, a, b);
                        }
                    }
                }
                None
            }
            _ => None,
        }
    }

    fn condition_to_guard(&self, cond: &Condition<AcWord>) -> Guard {
        match cond {
            Condition::And(c1, c2) => Guard::And(vec![
                self.condition_to_guard(c1),
                self.condition_to_guard(c2),
            ]),
            Condition::Or(c1, c2) => Guard::Or(vec![
                self.condition_to_guard(c1),
                self.condition_to_guard(c2),
            ]),
            Condition::Not(cond) => self.condition_to_guard(cond).negate_whole(),
            Condition::Eval(cmd) | Condition::ReturnZero(cmd) => Guard::N(true, Atom::Cmd(**cmd)),
            Condition::Cond(op) => match op {
                Operator::Eq(w1, w2) => {
                    let atom = if let Some(res) = self.equality(w1, w2) {
                        res
                    } else if let Some(res) = self.equality(w2, w1) {
                        res
                    } else {
                        dbg!(w1, w2);
                        panic!("unsupported syntax");
                    };
                    Guard::confirmed(atom)
                }
                Operator::Neq(w1, w2) => {
                    let atom = if let Some(res) = self.equality(w1, w2) {
                        res
                    } else if let Some(res) = self.equality(w2, w1) {
                        res
                    } else {
                        dbg!(w1, w2);
                        panic!("unsupported syntax");
                    };
                    Guard::negated(atom)
                }
                Operator::Ge(w1, w2) => {
                    let atom = if let Some(v1) = as_shell(w1).and_then(as_var) {
                        if let Some(v2) = as_shell(w2).and_then(as_vol) {
                            Atom::Var(v1.to_owned(), VarCond::Ge(v2))
                        } else {
                            panic!("unsupported syntax");
                        }
                    } else if let Some(v2) = as_shell(w2).and_then(as_var) {
                        if let Some(v1) = as_shell(w1).and_then(as_vol) {
                            Atom::Var(v2.to_owned(), VarCond::Le(v1))
                        } else {
                            panic!("unsupported syntax");
                        }
                    } else {
                        panic!("unsupported syntax");
                    };
                    Guard::confirmed(atom)
                }
                Operator::Gt(w1, w2) => {
                    let atom = if let Some(v1) = as_shell(w1).and_then(as_var) {
                        if let Some(v2) = as_shell(w2).and_then(as_vol) {
                            Atom::Var(v1.to_owned(), VarCond::Gt(v2))
                        } else {
                            panic!("unsupported syntax");
                        }
                    } else if let Some(v2) = as_shell(w2).and_then(as_var) {
                        if let Some(v1) = as_shell(w1).and_then(as_vol) {
                            Atom::Var(v2.to_owned(), VarCond::Lt(v1))
                        } else {
                            panic!("unsupported syntax");
                        }
                    } else {
                        dbg!(w1, w2);
                        panic!("unsupported syntax");
                    };
                    Guard::confirmed(atom)
                }
                Operator::Le(w1, w2) => {
                    let atom = if let Some(v1) = as_shell(w1).and_then(as_var) {
                        if let Some(v2) = as_shell(w2).and_then(as_vol) {
                            Atom::Var(v1.to_owned(), VarCond::Le(v2))
                        } else {
                            panic!("unsupported syntax");
                        }
                    } else if let Some(v2) = as_shell(w2).and_then(as_var) {
                        if let Some(v1) = as_shell(w1).and_then(as_vol) {
                            Atom::Var(v2.to_owned(), VarCond::Ge(v1))
                        } else {
                            panic!("unsupported syntax");
                        }
                    } else {
                        panic!("unsupported syntax");
                    };
                    Guard::confirmed(atom)
                }
                Operator::Lt(w1, w2) => {
                    let atom = if let Some(v2) = as_shell(w2).and_then(as_var) {
                        if let Some(v1) = as_shell(w1).and_then(as_vol) {
                            Atom::Var(v2.to_owned(), VarCond::Lt(v1))
                        } else {
                            panic!("unsupported syntax");
                        }
                    } else if let Some(v2) = as_shell(w2).and_then(as_var) {
                        if let Some(v1) = as_shell(w1).and_then(as_vol) {
                            Atom::Var(v2.to_owned(), VarCond::Gt(v1))
                        } else {
                            panic!("unsupported syntax");
                        }
                    } else {
                        panic!("unsupported syntax");
                    };
                    Guard::confirmed(atom)
                }
                Operator::Empty(w) => {
                    if let Some(name) = as_shell(w).and_then(as_var) {
                        Guard::confirmed(Atom::Var(name.to_owned(), VarCond::Empty))
                    } else {
                        panic!("unsupported syntax");
                    }
                }
                Operator::NonEmpty(w) => {
                    if let Some(name) = as_shell(w).and_then(as_var) {
                        Guard::negated(Atom::Var(name.to_owned(), VarCond::Empty))
                    } else {
                        panic!("unsupported syntax");
                    }
                }
                Operator::Dir(w) | Operator::File(w) => {
                    let (path, is_absolute) = analyze_path(w);
                    Guard::confirmed(Atom::PathExists(path, is_absolute))
                }
                Operator::NoExists(w) => {
                    let (path, is_absolute) = analyze_path(w);
                    Guard::negated(Atom::PathExists(path, is_absolute))
                }
            },
        }
    }

    fn pattern_to_guard(&self, word: &AcWord, pattern: &AcWord) -> Option<Guard> {
        if let Some(word) = as_shell(word) {
            let word = if let &WordFragment::DoubleQuoted(frags) = &word {
                if frags.len() == 1 {
                    frags.first().clone().unwrap()
                } else {
                    word
                }
            } else {
                word
            };
            if let WordFragment::Subst(subst) = &word {
                match &**subst {
                    ParameterSubstitution::Command(cmds) if cmds.len() == 1 => {
                        Some(Guard::confirmed(Atom::Cmd(cmds.first().unwrap().clone())))
                    }
                    _ => None,
                }
            } else if let Some(var) = as_var(word) {
                match &pattern.0 {
                    Word::Empty => {
                        Some(Guard::confirmed(Atom::Var(var.to_owned(), VarCond::Empty)))
                    }
                    Word::Single(MayM4::Shell(pat)) => {
                        if let Some(lit) = as_literal(pat) {
                            if var == "host_cpu" {
                                Some(Guard::confirmed(Atom::ArchGlob(lit.to_owned())))
                            } else if var == "host_os" {
                                Some(Guard::confirmed(Atom::OsAbiGlob(lit.to_owned())))
                            } else {
                                let cond = if lit == "yes" {
                                    VarCond::Yes
                                } else if lit == "no" {
                                    VarCond::No
                                } else if lit.is_empty() {
                                    VarCond::Empty
                                } else {
                                    VarCond::Eq(VoL::Lit(lit.to_owned()))
                                };
                                Some(Guard::confirmed(Atom::Var(var.to_owned(), cond)))
                            }
                        } else if let &WordFragment::Star = pat {
                            Some(Guard::confirmed(Atom::Var(
                                var.to_owned(),
                                VarCond::MatchAny,
                            )))
                        } else {
                            None
                        }
                    }
                    _ => {
                        let pattern_string = self.pool.display_word(pattern, false);
                        if var == "host" {
                            let (arch, _, os): (String, String, String) =
                                split_glob_triplet(&pattern_string)
                                    .into_iter()
                                    .take(3)
                                    .tuples()
                                    .collect();
                            if arch != "*" && os != "*" {
                                Some(Guard::And(vec![
                                    Guard::confirmed(Atom::ArchGlob(arch)),
                                    Guard::confirmed(Atom::OsAbiGlob(os)),
                                ]))
                            } else if arch != "*" {
                                Some(Guard::confirmed(Atom::ArchGlob(arch)))
                            } else if os != "*" {
                                Some(Guard::confirmed(Atom::OsAbiGlob(os)))
                            } else {
                                Some(Guard::confirmed(Atom::Var(
                                    var.to_owned(),
                                    VarCond::MatchAny,
                                )))
                            }
                        } else if var == "host_cpu" {
                            Some(Guard::confirmed(Atom::ArchGlob(pattern_string)))
                        } else if pattern_string.contains("*")
                            || pattern_string.contains("[")
                            || pattern_string.contains("]")
                            || pattern_string.contains("?")
                        {
                            Some(Guard::confirmed(Atom::Var(
                                var.to_owned(),
                                VarCond::Match(pattern_string),
                            )))
                        } else {
                            Some(Guard::confirmed(Atom::Var(
                                var.to_owned(),
                                VarCond::Eq(VoL::Lit(pattern_string)),
                            )))
                        }
                    }
                }
            } else if let &WordFragment::DoubleQuoted(ref frags) = word {
                let pattern_string = self.pool.display_word(pattern, false);
                let vars: Vec<String> = frags
                    .iter()
                    .filter_map(as_var)
                    .map(|s| s.to_owned())
                    .collect();
                let guard = Guard::make_or(
                    vars.into_iter()
                        .map(|var| {
                            Guard::confirmed(Atom::Var(var, VarCond::Match(pattern_string.clone())))
                        })
                        .collect(),
                );
                Some(guard)
            } else {
                None
            }
        } else {
            None
        }
    }
}

impl<'a> AstVisitor for GuardAnalyzer<'a> {
    fn get_node(&self, node_id: NodeId) -> &Node {
        &self.pool.nodes[node_id]
    }

    fn visit_top(&mut self, node_id: NodeId) {
        self.cursor.replace(node_id);
        self.walk_node(node_id);
    }

    fn visit_node(&mut self, node_id: NodeId) {
        let saved_cursor = self.cursor.replace(node_id);

        if !self.get_node(node_id).info.is_top_node() {
            self.walk_node(node_id);
        }

        self.cursor = saved_cursor;
    }

    fn visit_condition(&mut self, cond: &Condition<AcWord>) {
        let guard = self.condition_to_guard(cond);
        self.guard_stack.push(guard);
        if let Condition::Eval(cmd) | Condition::ReturnZero(cmd) = cond {
            self.record_block(&[**cmd]);
        }
        self.walk_condition(cond);
    }

    fn visit_parameter_substitution(&mut self, subs: &ParameterSubstitution<AcWord>) {
        use autotools_parser::ast::ParameterSubstitution::*;
        if let Command(cmds) = subs {
            self.record_block(cmds);
        }
        self.walk_parameter_substitution(subs);
    }

    // Note that in this implementation, this method is not called by visit_if.
    // Only visit_while and visit_until will call it,
    fn visit_guard_body_pair(&mut self, pair: &GuardBodyPair<AcWord>) {
        self.visit_condition(&pair.condition);
        self.record_block(&pair.body);
        for c in &pair.body {
            self.visit_node(*c);
        }
        self.guard_stack.pop();
    }

    fn visit_for(&mut self, var: &str, words: &[AcWord], body: &[NodeId]) {
        self.record_block(body);
        self.walk_for(var, words, body);
    }

    fn visit_if(&mut self, conditionals: &[GuardBodyPair<AcWord>], else_branch: &[NodeId]) {
        let saved_stack = self.guard_stack.clone();
        for pair in conditionals.iter() {
            self.visit_condition(&pair.condition);
            self.record_block(&pair.body);
            for c in &pair.body {
                self.visit_node(*c);
            }
            self.negate_last_guard();
        }
        if !else_branch.is_empty() {
            self.record_block(&else_branch);
        }
        for c in else_branch {
            self.visit_node(*c);
        }
        self.guard_stack = saved_stack;
    }

    fn visit_and_or(&mut self, negated: bool, condition: &Condition<AcWord>, cmd: NodeId) {
        self.visit_condition(condition);
        if negated {
            self.negate_last_guard();
        }
        self.record_block(&[cmd]);
        self.walk_node(cmd);
        self.guard_stack.pop();
    }

    fn visit_pipe(&mut self, bang: bool, cmds: &[NodeId]) {
        self.record_block(cmds);
        self.walk_pipe(bang, cmds);
    }

    fn visit_redirect(&mut self, cmd: NodeId, redirects: &[Redirect<AcWord>]) {
        self.record_block(&[cmd]);
        self.walk_redirect(cmd, redirects);
    }

    fn visit_case(&mut self, word: &AcWord, arms: &[PatternBodyPair<AcWord>]) {
        let saved_stack = self.guard_stack.clone();
        for arm in arms {
            let guard = Guard::make_or(
                arm.patterns
                    .iter()
                    .map(|pattern| {
                        self.pattern_to_guard(word, pattern)
                            .expect("unsupported syntax")
                    })
                    .collect(),
            );
            self.guard_stack.push(guard);
            self.record_block(&arm.body);
            for c in &arm.body {
                self.visit_node(*c);
            }
            self.negate_last_guard();
        }
        self.guard_stack = saved_stack;
    }

    fn visit_m4_macro(&mut self, m4_macro: &M4Macro) {
        for arg in m4_macro.args.iter() {
            match arg {
                M4Argument::Condition(cond) => {
                    self.visit_condition(cond);
                    self.record_block(&[]);
                    self.guard_stack.pop();
                }
                M4Argument::Commands(cmds) => {
                    self.record_block(cmds);
                }
                _ => {}
            }
        }
        self.walk_m4_macro(m4_macro);
    }
}

fn analyze_path(word: &AcWord) -> (Vec<VoL>, bool) {
    let mut words = match &word.0 {
        Word::Empty => panic!("unsupported syntax"),
        Word::Concat(words) => {
            let mut v = Vec::new();
            for w in words {
                if let MayM4::Shell(w) = w {
                    v.push(w);
                } else {
                    panic!("unsupported syntax");
                }
            }
            v
        }
        Word::Single(w) => {
            if let MayM4::Shell(w) = w {
                vec![w]
            } else {
                panic!("unsupported syntax");
            }
        }
    };
    let is_absolute = {
        if words
            .first()
            .and_then(|w| as_literal(w))
            .is_some_and(|s| s == "\\")
        {
            words.remove(0);
            true
        } else {
            false
        }
    };
    if words.len() > 1
        && !words[1..]
            .into_iter()
            .step_by(2)
            .all(|w| as_literal(w).is_some_and(|s| s == "\\"))
    {
        panic!("unsupported syntax");
    }
    let path = words.iter().step_by(2).filter_map(|w| as_vol(w)).collect();
    (path, is_absolute)
}

fn split_glob_triplet(s: &str) -> Vec<String> {
    let mut parts = Vec::new();
    let mut buf = String::new();
    let mut in_bracket = false;

    for c in s.chars() {
        match c {
            '[' => {
                in_bracket = true;
                buf.push(c);
            }
            ']' => {
                in_bracket = false;
                buf.push(c);
            }
            '-' if !in_bracket => {
                parts.push(buf);
                buf = String::new();
            }
            _ => buf.push(c),
        }
    }
    parts.push(buf);
    parts
}
