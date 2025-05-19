use std::collections::{HashMap, HashSet};

use super::{AstVisitor, Node, TopLevelCommand};
use autoconf_parser::ast::{
    minimal::{Command, CommandWrapper, CompoundCommand, GuardBodyPair},
    PatternBodyPair,
};

/// A visitor to flatten and collect AST nodes into a linear sequence.
#[derive(Debug)]
pub(super) struct Flattener {
    threshold: usize,
    pub nodes: Vec<Node>,
    parent_stack: Vec<usize>,
    last_range_start: Option<usize>,
}

impl Flattener {
    pub fn new(threshold: usize) -> Self {
        Self {
            threshold,
            nodes: Vec::new(),
            parent_stack: vec![],
            last_range_start: None,
        }
    }
}

impl AstVisitor for Flattener {
    fn visit_command_wrapper(&mut self, c: &TopLevelCommand) {
        let do_flatten = c.range.is_some_and(|(a, b)| b - a > self.threshold);

        match &c.cmd {
            // Flatten bare braces (drop the wrapper entirely)
            Command::Compound(CompoundCommand::Brace(body)) if do_flatten => {
                for nested in body {
                    self.visit_command_wrapper(nested);
                }
            }
            // Flatten for-loops: keep header, drop body but schedule nested bodies as children
            Command::Compound(CompoundCommand::For { var, words, body }) if do_flatten => {
                let id = self.nodes.len();
                let parent = self.parent_stack.last().cloned();
                let (start, end) = c.range.unwrap();
                let first = body.first().unwrap().range.unwrap().0;
                let last = body.last().unwrap().range.unwrap().1;
                let ranges = vec![(start, first), (last, end)];

                let cmd = Command::Compound(CompoundCommand::For {
                    var: var.clone(),
                    words: words.clone(),
                    body: Vec::new(),
                });

                if let (Some(prev), Some(curr)) =
                    (self.last_range_start, ranges.first().map(|&(s, _)| s))
                {
                    if !(prev <= curr) {
                        dbg!(&ranges, id, self.last_range_start);
                        panic!();
                    }
                }

                self.last_range_start = ranges.first().map(|&(s, _)| s);
                self.nodes.push(Node {
                    id,
                    comment: c.comment.clone(),
                    ranges,
                    cmd,
                    parent,
                    children: None,
                    defines: HashMap::new(),
                    uses: HashMap::new(),
                    var_dependencies: HashSet::new(),
                    var_dependents: HashSet::new(),
                });

                self.parent_stack.push(id);
                for nested in body {
                    self.visit_command_wrapper(nested);
                }
                self.parent_stack.pop();
            }
            // Flatten case statements: keep patterns, drop bodies but schedule nested bodies as children
            Command::Compound(CompoundCommand::Case { word, arms }) if do_flatten => {
                let id = self.nodes.len();
                let parent = self.parent_stack.last().cloned();
                let whole = c.range.unwrap();
                let mut ranges = Vec::new();
                let header = (
                    whole.0,
                    arms.first().unwrap().body.first().unwrap().range.unwrap().0 - 1,
                );
                let footer = (
                    arms.last().unwrap().body.last().unwrap().range.unwrap().1 + 1,
                    whole.1,
                );

                ranges.push(header);
                let mut flat_arms = Vec::new();
                for arm in arms.iter() {
                    let pattern_start = arm.body.first().unwrap().range.unwrap().0 - 1;
                    flat_arms.push(PatternBodyPair {
                        patterns: arm.patterns.clone(),
                        body: Vec::new(),
                    });
                    ranges.push((pattern_start, pattern_start + 1));
                }
                ranges.push(footer);

                let cmd = Command::Compound(CompoundCommand::Case {
                    word: word.clone(),
                    arms: flat_arms,
                });
                if let (Some(prev), Some(curr)) =
                    (self.last_range_start, ranges.first().map(|&(s, _)| s))
                {
                    if !(prev <= curr) {
                        dbg!(&ranges, id, self.last_range_start);
                        panic!();
                    }
                }
                self.last_range_start = ranges.first().map(|&(s, _)| s);

                self.nodes.push(Node {
                    id,
                    comment: c.comment.clone(),
                    ranges,
                    cmd,
                    parent,
                    children: None,
                    defines: HashMap::new(),
                    uses: HashMap::new(),
                    var_dependencies: HashSet::new(),
                    var_dependents: HashSet::new(),
                });

                for arm in arms.iter() {
                    let body_range = arm
                        .body
                        .first()
                        .map(|c| c.range.unwrap().0)
                        .zip(arm.body.last().map(|c| c.range.unwrap().1))
                        .unwrap();
                    let nested = CommandWrapper {
                        comment: None,
                        range: Some(body_range),
                        cmd: Command::Compound(CompoundCommand::Brace(arm.body.clone())),
                    };
                    self.parent_stack.push(id);
                    self.visit_command_wrapper(&nested);
                    self.parent_stack.pop();
                }
            }
            // Flatten if-statements: keep conditions, drop then-bodies but schedule nested bodies as children
            Command::Compound(CompoundCommand::If {
                conditionals,
                else_branch,
            }) if do_flatten => {
                let id = self.nodes.len();
                let parent = self.parent_stack.last().cloned();

                let mut flat_conds = Vec::new();
                for GuardBodyPair { condition, body: _ } in conditionals.iter() {
                    flat_conds.push(GuardBodyPair {
                        condition: condition.clone(),
                        body: Vec::new(),
                    });
                }

                let cmd = Command::Compound(CompoundCommand::If {
                    conditionals: flat_conds,
                    else_branch: else_branch.clone(),
                });
                let ranges = vec![c.range.unwrap()];
                if let (Some(prev), Some(curr)) =
                    (self.last_range_start, ranges.first().map(|r| r.0))
                {
                    if !(prev <= curr) {
                        dbg!(&ranges, id, self.last_range_start);
                        panic!();
                    }
                }
                self.last_range_start = ranges.first().map(|r| r.0);

                self.nodes.push(Node {
                    id,
                    comment: c.comment.clone(),
                    ranges,
                    cmd,
                    parent,
                    children: None,
                    defines: HashMap::new(),
                    uses: HashMap::new(),
                    var_dependencies: HashSet::new(),
                    var_dependents: HashSet::new(),
                });

                for GuardBodyPair { condition: _, body } in conditionals.iter() {
                    let body_range = body
                        .first()
                        .map(|c| c.range.unwrap().0)
                        .zip(body.last().map(|c| c.range.unwrap().1))
                        .unwrap();
                    let nested = CommandWrapper {
                        comment: None,
                        range: Some(body_range),
                        cmd: Command::Compound(CompoundCommand::Brace(body.clone())),
                    };
                    self.parent_stack.push(id);
                    self.visit_command_wrapper(&nested);
                    self.parent_stack.pop();
                }
            }
            // Default: record node and recurse
            _ => {
                let id = self.nodes.len();
                let parent = self.parent_stack.last().cloned();
                let ranges = c.range.map_or_else(Vec::new, |r| vec![r]);

                if let (Some(prev), Some(curr)) =
                    (self.last_range_start, ranges.first().map(|r| r.0))
                {
                    if !(prev <= curr) {
                        dbg!(&ranges, id, self.last_range_start);
                        panic!();
                    }
                }
                self.last_range_start = ranges.first().map(|r| r.0);

                let cmd = c.cmd.clone();
                self.nodes.push(Node {
                    id,
                    comment: c.comment.clone(),
                    ranges,
                    cmd,
                    parent,
                    children: None,
                    defines: HashMap::new(),
                    uses: HashMap::new(),
                    var_dependencies: HashSet::new(),
                    var_dependents: HashSet::new(),
                });
            }
        }
    }
}
