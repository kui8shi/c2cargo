//! Provides the higher level on-time analyses to improve parsing
use autoconf_parser::{
    ast::{
        node::{
            Condition, GuardBodyPair, M4Argument, M4Macro, NodeId, NodeKind, NodePool, Operator,
            ParameterSubstitution, PatternBodyPair, Redirect, Word, WordFragment,
        },
        Arithmetic, Parameter,
    },
    lexer::Lexer,
    parse::NodeParser,
};
use std::collections::{HashMap, HashSet};

use case::{CaseAnalyzer, CaseMatch};
use eval::{EvalAnalyzer, EvalMatch};
use flatten::Flattener;
use variable::VariableAnalyzer;

use slab::Slab;

mod case;
mod eval;
mod flatten;
mod variable;

type Command = NodeKind<String>;

/// Visitor trait for walking over the AST nodes.
pub trait AstVisitor: Sized {
    /// Return Node from NodeId
    fn get_node(&self, node_id: NodeId) -> &Node;

    /// Entry function for visiting a top-level AST node.
    fn visit_top(&mut self, node_id: NodeId) {
        self.walk_node(node_id);
    }

    /// Intermediate function for visiting an AST node.
    fn visit_node(&mut self, node_id: NodeId) {
        if !self.get_node(node_id).is_top_node() {
            self.walk_node(node_id);
        }
    }

    /// Intermediate function for visiting a command.
    fn visit_command(&mut self, cmd_words: &[Word<String>]) {
        self.walk_command(cmd_words);
    }

    /// Intermediate function for visiting an assignment statement.
    fn visit_assignment(&mut self, name: &str, word: &Word<String>) {
        self.walk_assignment(name, word);
    }

    /// Intermediate function for visiting a brace statement
    fn visit_brace(&mut self, body: &[NodeId]) {
        self.walk_brace(body);
    }

    /// Intermediate function for visiting a guard-body pair (e.g., in while/until/if).
    fn visit_guard_body_pair(&mut self, pair: &GuardBodyPair<String>) {
        self.walk_guard_body_pair(pair);
    }

    /// Intermediate function for visiting a pattern-body pair (an arm in case).
    fn visit_pattern_body_pair(&mut self, arm: &PatternBodyPair<String>) {
        self.walk_pattern_body_pair(arm);
    }

    /// Intermediate function for visiting an `if` statement
    fn visit_if(&mut self, conditionals: &[GuardBodyPair<String>], else_branch: &[NodeId]) {
        self.walk_if(conditionals, else_branch);
    }

    /// Intermediate function for visiting a `for` statement
    fn visit_for(&mut self, var: &str, words: &[Word<String>], body: &[NodeId]) {
        self.walk_for(var, words, body);
    }

    /// Intermediate function for visiting a `case` statement
    fn visit_case(&mut self, word: &Word<String>, arms: &[PatternBodyPair<String>]) {
        self.walk_case(word, arms);
    }

    /// Intermediate function for visiting a word
    fn visit_word(&mut self, w: &Word<String>) {
        self.walk_word(w);
    }

    /// Intermediate function for visiting a word fragment
    fn visit_word_fragment(&mut self, f: &WordFragment<String>) {
        self.walk_word_fragment(f);
    }

    /// Intermediate function for visiting a pipe
    fn visit_pipe(&mut self, bang: bool, cmds: &[NodeId]) {
        self.walk_pipe(bang, cmds);
    }

    /// Intermediate function for visiting a command chain
    fn visit_chain(&mut self, negated: bool, condition: &Condition<String>, cmd: NodeId) {
        self.walk_chain(negated, condition, cmd);
    }

    /// Intermediate function for visiting a conditional expression.
    fn visit_condition(&mut self, cond: &Condition<String>) {
        self.walk_condition(cond);
    }

    /// Intermediate function for visiting an arithmetic expression.
    fn visit_arithmetic(&mut self, arith: &Arithmetic<String>) {
        self.walk_arithmetic(arith);
    }

    /// Intermediate function for visiting a parameter.
    fn visit_parameter(&mut self, param: &Parameter<String>) {
        self.walk_parameter(param);
    }

    /// Intermediate function for visiting a parameter substitution.
    fn visit_parameter_substitution(&mut self, subs: &ParameterSubstitution<String>) {
        self.walk_parameter_substitution(subs);
    }

    /// Intermediate function for visiting an IO redirect.
    fn visit_redirect(&mut self, cmd: NodeId, redirects: &[Redirect<String>]) {
        self.walk_redirect(cmd, redirects);
    }

    /// Intermediate function for visiting a M4 macro invocation.
    fn visit_m4_macro(&mut self, m4_macro: &M4Macro<String>) {
        self.walk_m4_macro(m4_macro);
    }

    /// Intermediate function for visiting a function definition.
    fn visit_function_definition(&mut self, name: &str, body: NodeId) {
        self.walk_function_definition(name, body);
    }

    /// Walk a node: wrappper of arbitrary command.
    fn walk_node(&mut self, node_id: NodeId) {
        let node = self.get_node(node_id);
        match &node.kind.clone() {
            NodeKind::Assignment(name, word) => self.visit_assignment(name, word),
            NodeKind::Cmd(words) => self.visit_command(words),
            NodeKind::Brace(body) => self.visit_brace(body),
            NodeKind::Subshell(body) => {
                for n in body {
                    self.visit_node(*n);
                }
            }
            NodeKind::While(pair) => self.visit_guard_body_pair(pair),
            NodeKind::Until(pair) => self.visit_guard_body_pair(pair),
            NodeKind::If {
                conditionals,
                else_branch,
            } => {
                self.visit_if(conditionals, else_branch);
            }
            NodeKind::For { var, words, body } => self.visit_for(var, words, body),
            NodeKind::Case { word, arms } => self.visit_case(word, arms),
            NodeKind::And(condition, cmd) => self.visit_chain(true, condition, *cmd),
            NodeKind::Or(condition, cmd) => self.visit_chain(false, condition, *cmd),
            NodeKind::Pipe(bang, cmds) => self.visit_pipe(*bang, cmds),
            NodeKind::Redirect(cmd, redirects) => self.visit_redirect(*cmd, redirects),
            NodeKind::Background(cmd) => self.visit_node(*cmd),
            NodeKind::FunctionDef { name, body } => self.visit_function_definition(name, *body),
            NodeKind::Macro(m4_macro) => self.visit_m4_macro(m4_macro),
        };
    }

    /// Walk an assignment statement.
    fn walk_assignment(&mut self, _name: &str, word: &Word<String>) {
        self.visit_word(word);
    }

    /// Walk a brace statement.
    fn walk_brace(&mut self, body: &[NodeId]) {
        for n in body {
            self.visit_node(*n);
        }
    }

    /// Walk a command.
    fn walk_command(&mut self, cmd_words: &[Word<String>]) {
        for word in cmd_words {
            self.visit_word(word);
        }
    }

    /// Walk an `if` statement
    fn walk_if(&mut self, conditionals: &[GuardBodyPair<String>], else_branch: &[NodeId]) {
        for pair in conditionals {
            self.visit_guard_body_pair(pair);
        }
        for cmd in else_branch {
            self.visit_node(*cmd);
        }
    }

    /// Walk a `for` statement
    fn walk_for(&mut self, _var: &str, words: &[Word<String>], body: &[NodeId]) {
        for word in words {
            self.visit_word(word);
        }
        for cmd in body {
            self.visit_node(*cmd);
        }
    }

    /// Walk a `case` statement
    fn walk_case(&mut self, word: &Word<String>, arms: &[PatternBodyPair<String>]) {
        self.visit_word(word);
        for arm in arms {
            self.visit_pattern_body_pair(arm);
        }
    }

    /// Walk a guard-body pair node.
    fn walk_guard_body_pair(&mut self, pair: &GuardBodyPair<String>) {
        self.visit_condition(&pair.condition);
        for c in &pair.body {
            self.visit_node(*c);
        }
    }

    /// Walk a pattern-body pair node.
    fn walk_pattern_body_pair(&mut self, arm: &PatternBodyPair<String>) {
        for w in &arm.patterns {
            self.visit_word(w);
        }
        for c in &arm.body {
            self.visit_node(*c);
        }
    }

    /// Walk a pipe
    fn walk_pipe(&mut self, _bang: bool, cmds: &[NodeId]) {
        for cmd in cmds {
            self.visit_node(*cmd);
        }
    }

    /// Walk a command chain.
    fn walk_chain(&mut self, _negated: bool, condition: &Condition<String>, cmd: NodeId) {
        self.visit_condition(condition);
        self.visit_node(cmd);
    }

    /// Walk an IO redirect.
    fn walk_redirect(&mut self, cmd: NodeId, redirects: &[Redirect<String>]) {
        self.visit_node(cmd);
        for redirect in redirects {
            match redirect {
                Redirect::Read(_, w)
                | Redirect::Write(_, w)
                | Redirect::ReadWrite(_, w)
                | Redirect::Append(_, w)
                | Redirect::Clobber(_, w)
                | Redirect::Heredoc(_, w)
                | Redirect::DupRead(_, w)
                | Redirect::DupWrite(_, w) => self.visit_word(w),
            }
        }
    }

    /// Walk a word node.
    fn walk_word(&mut self, w: &Word<String>) {
        match w {
            Word::Concat(frags) => {
                for f in frags {
                    self.visit_word_fragment(f);
                }
            }
            Word::Single(f) => self.visit_word_fragment(f),
            Word::Empty => {}
        }
    }

    /// Walk a word fragment node.
    fn walk_word_fragment(&mut self, f: &WordFragment<String>) {
        match f {
            WordFragment::Param(param) => self.visit_parameter(param),
            WordFragment::DoubleQuoted(frags) => {
                for f in frags {
                    self.visit_word_fragment(f);
                }
            }
            WordFragment::Macro(m4) => self.visit_m4_macro(m4),
            WordFragment::Subst(subst) => self.visit_parameter_substitution(subst.as_ref()),
            _ => {}
        }
    }

    /// Walk a conditional expression.
    fn walk_condition(&mut self, cond: &Condition<String>) {
        match cond {
            Condition::Cond(op) => match op {
                Operator::Eq(w1, w2)
                | Operator::Neq(w1, w2)
                | Operator::Ge(w1, w2)
                | Operator::Gt(w1, w2)
                | Operator::Le(w1, w2)
                | Operator::Lt(w1, w2) => {
                    self.visit_word(w1);
                    self.visit_word(w2);
                }
                Operator::Empty(w)
                | Operator::NonEmpty(w)
                | Operator::Dir(w)
                | Operator::File(w)
                | Operator::NoExists(w) => self.visit_word(w),
            },
            Condition::And(c1, c2) | Condition::Or(c1, c2) => {
                self.visit_condition(c1);
                self.visit_condition(c2);
            }
            Condition::Eval(cmds) => {
                for cmd in cmds {
                    self.visit_node(*cmd);
                }
            }
            Condition::ReturnZero(cmd) => self.visit_node(**cmd),
        }
    }

    /// Walk an arithmetic expression node.
    fn walk_arithmetic(&mut self, arith: &Arithmetic<String>) {
        match arith {
            Arithmetic::UnaryPlus(x)
            | Arithmetic::UnaryMinus(x)
            | Arithmetic::LogicalNot(x)
            | Arithmetic::BitwiseNot(x) => self.visit_arithmetic(x),
            Arithmetic::Pow(x, y)
            | Arithmetic::Mult(x, y)
            | Arithmetic::Div(x, y)
            | Arithmetic::Modulo(x, y)
            | Arithmetic::Add(x, y)
            | Arithmetic::Sub(x, y)
            | Arithmetic::ShiftLeft(x, y)
            | Arithmetic::ShiftRight(x, y)
            | Arithmetic::Less(x, y)
            | Arithmetic::LessEq(x, y)
            | Arithmetic::Great(x, y)
            | Arithmetic::GreatEq(x, y)
            | Arithmetic::Eq(x, y)
            | Arithmetic::NotEq(x, y)
            | Arithmetic::BitwiseAnd(x, y)
            | Arithmetic::BitwiseXor(x, y)
            | Arithmetic::BitwiseOr(x, y)
            | Arithmetic::LogicalAnd(x, y)
            | Arithmetic::LogicalOr(x, y) => {
                self.visit_arithmetic(x);
                self.visit_arithmetic(y);
            }
            Arithmetic::Ternary(x, y, z) => {
                self.visit_arithmetic(x);
                self.visit_arithmetic(y);
                self.visit_arithmetic(z);
            }
            Arithmetic::Sequence(seq) => {
                for a in seq {
                    self.visit_arithmetic(a);
                }
            }
            _ => {}
        }
    }

    /// Walk a parameter node.
    fn walk_parameter(&mut self, param: &Parameter<String>) {}

    /// Walk a parameter substitution node.
    fn walk_parameter_substitution(&mut self, subs: &ParameterSubstitution<String>) {
        match subs {
            ParameterSubstitution::Command(cmds) => {
                for c in cmds {
                    self.visit_node(*c);
                }
            }
            ParameterSubstitution::Arith(Some(arith)) => self.visit_arithmetic(arith),
            ParameterSubstitution::Len(param) => self.visit_parameter(param),
            ParameterSubstitution::Default(_, param, word)
            | ParameterSubstitution::Assign(_, param, word)
            | ParameterSubstitution::Error(_, param, word)
            | ParameterSubstitution::Alternative(_, param, word)
            | ParameterSubstitution::RemoveSmallestSuffix(param, word)
            | ParameterSubstitution::RemoveLargestSuffix(param, word)
            | ParameterSubstitution::RemoveSmallestPrefix(param, word)
            | ParameterSubstitution::RemoveLargestPrefix(param, word) => {
                self.visit_parameter(param);
                if let Some(w) = word {
                    self.visit_word(w);
                }
            }
            _ => {}
        }
    }

    /// Walk a function definition.
    fn walk_function_definition(&mut self, name: &str, body: NodeId) {}

    /// Walk an M4 macro node (walks arguments only).
    fn walk_m4_macro(&mut self, m4_macro: &M4Macro<String>) {
        for arg in &m4_macro.args {
            match arg {
                M4Argument::Word(w) => self.visit_word(w),
                M4Argument::Array(ws) => {
                    for w in ws {
                        self.visit_word(w);
                    }
                }
                M4Argument::Commands(cmds) => {
                    for c in cmds {
                        self.visit_node(*c);
                    }
                }
                _ => {}
            }
        }
    }
}

/// Represents a node in the dependency graph
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Node {
    /// Index of the node in the original list
    pub node_id: NodeId,
    /// ID of the top-most parent node
    pub top_id: Option<NodeId>,
    /// trailing comments
    pub comment: Option<String>,
    /// Range of line numbers where the body is effectively referenced.
    pub ranges: Vec<(usize, usize)>,
    /// Body of commands referenced by this node.
    pub kind: NodeKind<String>,
    /// ID of the parent node and the branch index itself hangs on
    pub parent: Option<(NodeId, Option<usize>)>,
    /// IDs of the children
    pub children: Option<Vec<NodeId>>,
    /// Variables defined by this command
    pub defines: HashMap<String, Vec<Guard>>,
    /// Variables used by this command
    pub uses: HashMap<String, Vec<Guard>>,
    /// Dependencies (indices of nodes this command depends on by variables)
    pub var_dependencies: HashSet<NodeId>,
    /// Commands that depend on this node
    pub var_dependents: HashSet<NodeId>,
}

impl Node {
    pub fn range_start(&self) -> Option<usize> {
        self.ranges.first().map(|(start, _)| start).copied()
    }

    pub fn range_end(&self) -> Option<usize> {
        self.ranges.last().map(|(_, end)| end).copied()
    }

    pub fn is_top_node(&self) -> bool {
        self.top_id.is_some_and(|id| id == self.node_id)
    }

    pub fn is_child_node(&self) -> bool {
        self.parent.is_some()
    }
}

/// Represents a condition
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Guard {
    /// doc
    Not(Box<Self>),
    /// doc
    Cond(Condition<String>),
    /// doc
    Match(Word<String>, Vec<Word<String>>),
}

/// Analyzer which conducts various kinds of analyses:
/// 1. construction of a dependency graph by tracking variable usages
/// 2. flattening of large commands
/// etc..
#[derive(Debug)]
pub struct Analyzer {
    /// Original contents of analyzed script
    lines: Vec<String>,
    /// Nodes in the dependency graph
    nodes: Slab<Node>,
    /// Ids of top-level commands
    top_ids: Vec<NodeId>,
    /// Map of variable names to indices of commands that define them
    var_definitions: HashMap<String, Vec<(usize, Vec<Guard>)>>,
    /// Set of variable names of which are repeatedly used across the entire script
    global_vars: HashSet<String>,
    /// State field used for printing a node
    focus: Option<NodeId>,
}

impl Analyzer {
    /// Analyze commands and build the dependency graph
    pub fn new<S: AsRef<str>>(contents: S, flatten_threshold: Option<usize>) -> Self {
        let lexer = Lexer::new(contents.as_ref().chars());
        let (nodes, top_ids) = NodeParser::new(lexer).parse_all();

        let nodes = nodes
            .into_iter()
            .map(|(node_id, n)| {
                let node = Node {
                    node_id,
                    top_id: None,
                    comment: n.comment,
                    ranges: n.range.map_or(Vec::new(), |r| vec![r]),
                    kind: n.kind,
                    parent: None,
                    children: None,
                    defines: HashMap::new(),
                    uses: HashMap::new(),
                    var_dependents: HashSet::new(),
                    var_dependencies: HashSet::new(),
                };
                (node_id, node)
            })
            .collect::<Slab<Node>>();

        let (top_ids, mut nodes) =
            Flattener::flatten(nodes, top_ids, flatten_threshold.unwrap_or(200));

        let mut var_definitions = HashMap::new();

        // Create a VariableAnalyzer to extract both defined and used variables
        let mut va = VariableAnalyzer::new(&mut nodes);
        for &id in &top_ids {
            // collect all defined and used variables in a command
            va.analyze(id);

            // Update var_definitions map
            for (var, guards) in &va.defines {
                var_definitions
                    .entry(var.clone())
                    .or_insert_with(Vec::new)
                    .push((id, guards.clone()));
            }
        }

        let mut s = Self {
            lines: contents.as_ref().lines().map(|s| s.to_string()).collect(),
            nodes,
            top_ids,
            var_definitions: HashMap::new(),
            global_vars: HashSet::new(),
            focus: None,
        };

        let mut updates = Vec::new();

        // Create dependency edges based on variable usage
        for (id, node) in &s.nodes {
            for var in node.uses.keys() {
                if let Some(def_id) = s.get_definition(var, id) {
                    updates.push((def_id, id));
                }
            }
        }

        // Apply updates to nodes
        for (def_id, user_id) in updates {
            s.nodes[user_id].var_dependencies.insert(def_id);
            s.nodes[def_id].var_dependents.insert(user_id);
        }

        s
    }

    /// Get the number of nodes (commands)
    pub fn num_nodes(&self) -> usize {
        self.nodes.len()
    }

    /// Get command that define a variable before
    pub fn get_definition(&self, var_name: &str, node_id: NodeId) -> Option<usize> {
        if let Some(node) = self.nodes.get(node_id) {
            if let Some(user_guards) = node.uses.get(var_name) {
                return self.var_definitions.get(var_name).and_then(|v| {
                    v.iter()
                        .rev()
                        .filter_map(|(i, guards)| {
                            // dumb heulistic to compare two guard conditions
                            (*i < node_id && guards.len() <= user_guards.len()).then_some(i)
                        })
                        .next()
                        .cloned()
                });
            }
        }
        None
    }

    /// Get all variables defined by a command
    pub fn get_defined_variables(&self, node_id: NodeId) -> Option<HashSet<String>> {
        self.nodes
            .get(node_id)
            .map(|node| node.defines.keys().cloned().collect())
    }

    /// Get all variables used by a command
    pub fn get_used_variables(&self, node_id: NodeId) -> Option<HashSet<String>> {
        self.nodes
            .get(node_id)
            .map(|node| node.uses.keys().cloned().collect())
    }

    /// Get all commands this command depends on
    pub fn get_dependencies(&self, node_id: NodeId) -> Option<HashSet<NodeId>> {
        self.nodes
            .get(node_id)
            .map(|node| node.var_dependencies.clone())
    }

    pub fn get_parent(&self, node_id: NodeId) -> Option<(usize, Option<NodeId>)> {
        self.nodes[node_id].parent
    }

    /// Get all commands that depend on this command
    pub fn get_dependents(&self, node_id: NodeId) -> Option<HashSet<NodeId>> {
        self.nodes.get(node_id).map(|node| {
            let mut deps = node.var_dependencies.clone();
            if let Some(children) = &node.children {
                deps.extend(children.iter().copied());
            }
            deps
        })
    }

    /// Get vector of all node ids
    pub fn get_ids(&self) -> Vec<usize> {
        self.nodes.iter().map(|(id, _)| id).collect()
    }

    /// Get vector of all ids of top-level nodes
    pub fn get_top_ids(&self) -> Vec<usize> {
        self.top_ids.clone()
    }

    /// Get a range of the command at the specified index
    pub fn get_ranges(&self, id: NodeId) -> Option<&[(usize, usize)]> {
        self.nodes.get(id).map(|n| n.ranges.as_ref())
    }
    /// Get a reference to the command at the specified index
    pub fn get_command(&self, id: NodeId) -> Option<&Command> {
        self.nodes.get(id).map(|n| &n.kind)
    }

    /// Get all commands that define or use a variable
    pub fn find_commands_with_variable(&self, var_name: &str) -> HashSet<usize> {
        let mut result = HashSet::new();

        // Add commands that define the variable
        if let Some(def_indices) = self.var_definitions.get(var_name) {
            result.extend(def_indices.iter().map(|(i, _)| i));
        }

        // Add commands that use the variable
        for (id, node) in &self.nodes {
            if node.uses.contains_key(var_name) {
                result.insert(id);
            }
        }

        result
    }

    /// Get node representation by id
    pub fn get_node(&self, node_id: NodeId) -> &Node {
        &self.nodes[node_id]
    }

    /// Get original content of commands in specified node
    pub fn get_content(&self, node_id: NodeId) -> Option<Vec<String>> {
        self.nodes.get(node_id).map(|node| {
            node.ranges
                .iter()
                .map(|&(a, b)| {
                    // FIXME: Poorly working with this lines extraction logic.
                    // Will fix it later.
                    self.lines[a - 1..b - 1]
                        .iter()
                        .filter(|s| !s.is_empty())
                        .map(|s| s.as_str())
                        .collect::<Vec<_>>()
                        .join("\n")
                })
                .collect()
        })
    }

    /// Recover the content of commands from the AST structure
    pub fn recover_content(&mut self, node_id: NodeId) -> String {
        self.focus = Some(node_id);
        let ret = self.node_to_string(node_id, 0);
        self.focus = None;
        ret
    }

    /// Find case statements matching the given variables in the top-level commands.
    pub fn find_case_matches(&self, var_names: &[String]) -> Vec<CaseMatch> {
        let finder =
            CaseAnalyzer::find_case_matches(&self.nodes, &self.top_ids, var_names.to_vec());
        finder.matches
    }

    /// Find `eval` commands that generate dynamic variable references.
    pub fn find_eval_dynamic_refs(&self) -> Vec<EvalMatch> {
        let finder = EvalAnalyzer::find_eval_dynamic_refs(&self.nodes, &self.top_ids);
        finder.matches
    }

    /// Check if any node in a chunk is related to any node within a window of nodes.
    /// With window=1, this is equivalent to the original pairwise relation check.
    fn are_nodes_related_with_window(&self, chunk: &[NodeId], window_nodes: &[NodeId]) -> bool {
        for &chunk_node in chunk {
            for &window_node in window_nodes {
                if self.are_nodes_related(chunk_node, window_node) {
                    return true;
                }
            }
        }
        false
    }

    /// Check if two nodes are related for chunk fusing.
    /// Nodes are related if one depends on the other through variable dependencies.
    fn are_nodes_related(&self, node1_id: NodeId, node2_id: NodeId) -> bool {
        if let (Some(node1), Some(node2)) = (self.nodes.get(node1_id), self.nodes.get(node2_id)) {
            // Check if node2 depends on node1 or vice versa
            (node1.parent == node2.parent)
                && !(node1
                    .defines
                    .keys()
                    .filter(|key| !self.global_vars.contains(key.as_str()))
                    .cloned()
                    .collect::<HashSet<_>>())
                .is_disjoint(
                    &node2
                        .uses
                        .keys()
                        .cloned()
                        .collect::<HashSet<_>>(),
                )
        } else {
            false
        }
    }

    /// Check if a node is an assignment statement.
    fn is_assignment(&self, node_id: NodeId) -> bool {
        if let Some(node) = self.nodes.get(node_id) {
            matches!(node.kind, NodeKind::Assignment(_, _))
        } else {
            false
        }
    }

    /// Perform chunk fusing with speculative lookahead window.
    /// When window > 0, speculatively adds next `window` nodes and reverts if no relations found.
    /// When disrespect_assignment is true, assignment nodes are looked through without consuming window depth.
    pub fn fuse_chunks(
        &self,
        window: Option<usize>,
        disrespect_assignment: bool,
    ) -> Vec<Vec<NodeId>> {
        let window = window.unwrap_or(0);
        let mut chunks = Vec::new();
        let mut current_chunk = Vec::new();
        let mut i = 0;

        while i < self.top_ids.len() {
            let current_id = self.top_ids[i];

            if current_chunk.is_empty() {
                // Start a new chunk
                current_chunk.push(current_id);
            } else {
                // Check if current node has the same parent as nodes in current chunk
                let chunk_parent = self
                    .nodes
                    .get(*current_chunk.first().unwrap())
                    .map(|n| n.parent);
                let current_parent = self.nodes.get(current_id).map(|n| n.parent);
                let same_parent = chunk_parent == current_parent;

                // Check if current node is related to any node in the current chunk
                let is_related_to_chunk = same_parent
                    && current_chunk
                        .iter()
                        .any(|&chunk_node_id| self.are_nodes_related(chunk_node_id, current_id));

                if is_related_to_chunk {
                    // Fuse with current chunk
                    current_chunk.push(current_id);
                } else if window > 0 || disrespect_assignment {
                    // Try speculative lookahead with optional assignment skipping
                    let mut lookahead_nodes = Vec::new();
                    let mut j = i;
                    let mut remaining_window = window;

                    // Collect lookahead nodes, skipping assignments if disrespect_assignment is true
                    while j < self.top_ids.len()
                        && (remaining_window > 0
                            || (disrespect_assignment && self.is_assignment(self.top_ids[j])))
                    {
                        let node_id = self.top_ids[j];

                        // Check if this node has the same parent as the chunk
                        let node_parent = self.nodes.get(node_id).map(|n| n.parent);
                        if chunk_parent != node_parent {
                            break; // Different parent, stop lookahead
                        }

                        lookahead_nodes.push(node_id);

                        // Only consume window depth for non-assignments or when not disrespecting assignments
                        if !disrespect_assignment || !self.is_assignment(node_id) {
                            if remaining_window > 0 {
                                remaining_window -= 1;
                            } else {
                                break;
                            }
                        }

                        j += 1;
                    }

                    if self.are_nodes_related_with_window(&current_chunk, &lookahead_nodes) {
                        // Found relation within lookahead - add all lookahead nodes to chunk
                        current_chunk.extend(lookahead_nodes);
                        i = j - 1; // Skip ahead (will be incremented at loop end)
                    } else {
                        // No relation found in lookahead - cut here and start new chunk
                        if !current_chunk.is_empty() {
                            chunks.push(current_chunk.clone());
                            current_chunk.clear();
                        }
                        current_chunk.push(current_id);
                    }
                } else {
                    // No window - cut here and start new chunk
                    if !current_chunk.is_empty() {
                        chunks.push(current_chunk.clone());
                        current_chunk.clear();
                    }
                    current_chunk.push(current_id);
                }
            }
            i += 1;
        }

        // Add the last chunk if not empty
        if !current_chunk.is_empty() {
            chunks.push(current_chunk);
        }

        chunks
    }
}

impl NodePool<String> for Analyzer {
    fn get_node_for_display(
        &self,
        node_id: NodeId,
    ) -> Option<(&NodeKind<String>, Option<&String>)> {
        let is_child = self.focus.unwrap() != node_id;
        self.nodes
            .get(node_id)
            .filter(|n| n.is_top_node() ^ is_child)
            .map(|n| (&n.kind, n.comment.as_ref()))
    }
}
