//! Provides the higher level on-time analyses to improve parsing
use std::{
    cell::RefCell,
    cmp::Ordering,
    collections::{HashMap, HashSet},
    path::{Path, PathBuf},
};

use automake::AutomakeAnalyzer;
use autotools_parser::{
    ast::{
        minimal::Word,
        node::{
            AcCommand, AcWord, AcWordFragment, Condition, DisplayNode, GuardBodyPair, M4Argument,
            M4Macro, NodeId, Operator, ParameterSubstitution, PatternBodyPair, ShellCommand,
            WordFragment,
        },
        Arithmetic, MayM4, Parameter, Redirect,
    },
    lexer::Lexer,
    m4_macro::SideEffect,
    parse::autoconf::NodeParser,
};
use build_option::BuildOptionInfo;
use chunk::{Chunk, ChunkId, FunctionSkelton, Scope};
use dictionary::DictionaryInstance;
use guard::{Block, BlockId, Guard, GuardAnalyzer};
use itertools::Itertools;
use platform_support::PlatformSupport;
use project_info::ProjectInfo;
use type_inference::{DataType, TypeHint};

use flatten::Flattener;
use location::{ExecId, Location};
use value_set_analysis::{DividedVariable, VSACache};
use variable::{Identifier, ValueExpr, VariableAnalyzer};

use slab::Slab;

use crate::{
    analyzer::{
        conditional_compilation::ConditionalCompilationMap, macro_call::FixedMacroSideEffect,
    },
    display::AutoconfPool,
};

mod automake;
mod build_option;
mod chunk;
mod conditional_compilation;
mod dictionary;
mod filtering;
mod flatten;
mod guard;
mod location;
mod macro_call;
mod platform_support;
mod project_info;
mod removal;
mod translator;
mod type_inference;
mod value_set_analysis;
mod variable;

type VariableMap = HashMap<String, Vec<Location>>;
type NodeDependencyMap = HashMap<NodeId, HashSet<String>>;
type Node = autotools_parser::ast::node::Node<AcCommand, NodeInfo>;

fn as_shell(word: &AcWord) -> Option<&WordFragment<AcWord>> {
    if let Word::Single(MayM4::Shell(shell_word)) = &word.0 {
        Some(shell_word)
    } else {
        None
    }
}

fn as_literal(word: &WordFragment<AcWord>) -> Option<&str> {
    if let WordFragment::Literal(lit) = &word {
        Some(lit.as_str())
    } else {
        None
    }
}

fn as_var(word: &WordFragment<AcWord>) -> Option<&str> {
    if let WordFragment::Param(Parameter::Var(name)) = &word {
        Some(name.as_str())
    } else {
        None
    }
}

/// Visitor trait for walking over the AST nodes.
pub trait AstVisitor: Sized {
    /// Return Node from NodeId
    fn get_node(&self, node_id: NodeId) -> Option<&Node>;

    /// Entry function for visiting a top-level AST node.
    fn visit_top(&mut self, node_id: NodeId) {
        self.walk_node(node_id);
    }

    /// Intermediate function for visiting an AST node.
    fn visit_node(&mut self, node_id: NodeId) {
        if self
            .get_node(node_id)
            .is_some_and(|n| !n.info.is_top_node())
        {
            self.walk_node(node_id);
        }
    }

    /// Intermediate function for visiting a command.
    fn visit_command(&mut self, cmd_words: &[AcWord]) {
        self.walk_command(cmd_words);
    }

    /// Intermediate function for visiting an assignment statement.
    fn visit_assignment(&mut self, name: &str, word: &AcWord) {
        self.walk_assignment(name, word);
    }

    /// Intermediate function for visiting a brace statement
    fn visit_brace(&mut self, body: &[NodeId]) {
        self.walk_body(body);
    }

    /// Intermediate function for visiting a subshell.
    fn visit_subshell(&mut self, body: &[NodeId]) {
        self.walk_body(body);
    }

    /// Intermediate function for visiting a guard-body pair (e.g., in while/until/if).
    fn visit_guard_body_pair(&mut self, pair: &GuardBodyPair<AcWord>) {
        self.walk_guard_body_pair(pair);
    }

    /// Intermediate function for visiting an `if` statement
    fn visit_if(&mut self, conditionals: &[GuardBodyPair<AcWord>], else_branch: &[NodeId]) {
        self.walk_if(conditionals, else_branch);
    }

    /// Intermediate function for visiting a `for` statement
    fn visit_for(&mut self, var: &str, words: &[AcWord], body: &[NodeId]) {
        self.walk_for(var, words, body);
    }

    /// Intermediate function for visiting a `case` statement
    fn visit_case(&mut self, word: &AcWord, arms: &[PatternBodyPair<AcWord>]) {
        self.walk_case(word, arms);
    }

    /// Intermediate function for visiting a word
    fn visit_word(&mut self, w: &AcWord) {
        self.walk_word(w);
    }

    /// Intermediate function for visiting a word fragment
    fn visit_word_fragment(&mut self, f: &AcWordFragment) {
        self.walk_word_fragment(f);
    }

    /// Intermediate function for visiting a pipe
    fn visit_pipe(&mut self, bang: bool, cmds: &[NodeId]) {
        self.walk_pipe(bang, cmds);
    }

    /// Intermediate function for visiting a command chain
    fn visit_and_or(&mut self, negated: bool, condition: &Condition<AcWord>, cmd: NodeId) {
        self.walk_and_or(negated, condition, cmd);
    }

    /// Intermediate function for visiting a conditional expression.
    fn visit_condition(&mut self, cond: &Condition<AcWord>) {
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
    fn visit_parameter_substitution(&mut self, subs: &ParameterSubstitution<AcWord>) {
        self.walk_parameter_substitution(subs);
    }

    /// Intermediate function for visiting an IO redirect.
    fn visit_redirect(&mut self, cmd: NodeId, redirects: &[Redirect<AcWord>]) {
        self.walk_redirect(cmd, redirects);
    }

    /// Intermediate function for visiting a M4 macro invocation.
    fn visit_m4_macro(&mut self, m4_macro: &M4Macro) {
        self.walk_m4_macro(m4_macro);
    }

    /// Intermediate function for visiting a function definition.
    fn visit_function_definition(&mut self, name: &str, body: NodeId) {
        self.walk_function_definition(name, body);
    }

    fn visit_background(&mut self, cmd: NodeId) {
        self.walk_node(cmd);
    }

    /// Walk a node: wrappper of arbitrary command.
    fn walk_node(&mut self, node_id: NodeId) {
        use autotools_parser::ast::node::ShellCommand::*;
        use MayM4::*;
        if let Some(node) = self.get_node(node_id) {
            match &node.cmd.0.clone() {
                Shell(Assignment(name, word)) => self.visit_assignment(name, word),
                Shell(Cmd(words)) => self.visit_command(words),
                Shell(Brace(body)) => self.visit_brace(body),
                Shell(Subshell(body)) => self.visit_subshell(body),
                Shell(While(pair)) => self.visit_guard_body_pair(pair),
                Shell(Until(pair)) => self.visit_guard_body_pair(pair),
                Shell(If {
                    conditionals,
                    else_branch,
                }) => {
                    self.visit_if(conditionals, else_branch);
                }
                Shell(For { var, words, body }) => self.visit_for(var, words, body),
                Shell(Case { word, arms }) => self.visit_case(word, arms),
                Shell(And(condition, cmd)) => self.visit_and_or(true, condition, *cmd),
                Shell(Or(condition, cmd)) => self.visit_and_or(false, condition, *cmd),
                Shell(Pipe(bang, cmds)) => self.visit_pipe(*bang, cmds),
                Shell(Redirect(cmd, redirects)) => self.visit_redirect(*cmd, redirects),
                Shell(Background(cmd)) => self.visit_background(*cmd),
                Shell(FunctionDef { name, body }) => self.visit_function_definition(name, *body),
                Macro(m4_macro) => self.visit_m4_macro(m4_macro),
            };
        }
    }

    /// Walk an assignment statement.
    fn walk_assignment(&mut self, _name: &str, word: &AcWord) {
        self.visit_word(word);
    }

    /// Walk a brace statement.
    fn walk_body(&mut self, body: &[NodeId]) {
        for n in body {
            self.visit_node(*n);
        }
    }

    /// Walk a command.
    fn walk_command(&mut self, cmd_words: &[AcWord]) {
        for word in cmd_words {
            self.visit_word(word);
        }
    }

    /// Walk an `if` statement
    fn walk_if(&mut self, conditionals: &[GuardBodyPair<AcWord>], else_branch: &[NodeId]) {
        for pair in conditionals {
            self.visit_guard_body_pair(pair);
        }
        for cmd in else_branch {
            self.visit_node(*cmd);
        }
    }

    /// Walk a `for` statement
    fn walk_for(&mut self, _var: &str, words: &[AcWord], body: &[NodeId]) {
        for word in words {
            self.visit_word(word);
        }
        for cmd in body {
            self.visit_node(*cmd);
        }
    }

    /// Walk a `case` statement
    fn walk_case(&mut self, word: &AcWord, arms: &[PatternBodyPair<AcWord>]) {
        self.visit_word(word);
        for arm in arms {
            self.walk_pattern_body_pair(arm);
        }
    }

    /// Walk a pattern-body pair node.
    fn walk_pattern_body_pair(&mut self, arm: &PatternBodyPair<AcWord>) {
        for w in &arm.patterns {
            self.visit_word(w);
        }
        for c in &arm.body {
            self.visit_node(*c);
        }
    }

    /// Walk a guard-body pair node.
    fn walk_guard_body_pair(&mut self, pair: &GuardBodyPair<AcWord>) {
        self.visit_condition(&pair.condition);
        for c in &pair.body {
            self.visit_node(*c);
        }
    }

    /// Walk a pipe
    fn walk_pipe(&mut self, _bang: bool, cmds: &[NodeId]) {
        for cmd in cmds {
            self.visit_node(*cmd);
        }
    }

    /// Walk commands concatenated via and/or.
    fn walk_and_or(&mut self, _negated: bool, condition: &Condition<AcWord>, cmd: NodeId) {
        self.visit_condition(condition);
        self.visit_node(cmd);
    }

    /// Walk an IO redirect.
    fn walk_redirect(&mut self, cmd: NodeId, redirects: &[Redirect<AcWord>]) {
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
    fn walk_word(&mut self, w: &AcWord) {
        use Word::*;
        match &w.0 {
            Concat(frags) => {
                for f in frags {
                    self.visit_word_fragment(f);
                }
            }
            Single(f) => self.visit_word_fragment(f),
            Empty => {}
        }
    }

    /// Walk a word fragment node.
    fn walk_word_fragment(&mut self, f: &AcWordFragment) {
        use autotools_parser::ast::minimal::WordFragment::*;
        use MayM4::*;
        match f {
            Shell(Param(param)) => self.visit_parameter(param),
            Shell(DoubleQuoted(frags)) => {
                for f in frags {
                    self.visit_word_fragment(&Shell(f.clone()));
                }
            }
            Shell(Subst(subst)) => self.visit_parameter_substitution(subst.as_ref()),
            Macro(m4) => self.visit_m4_macro(m4),
            _ => {}
        }
    }

    /// Walk a conditional expression.
    fn walk_condition(&mut self, cond: &Condition<AcWord>) {
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
            Condition::Not(cond) => self.visit_condition(cond),
            Condition::And(c1, c2) | Condition::Or(c1, c2) => {
                self.visit_condition(c1);
                self.visit_condition(c2);
            }
            Condition::Eval(cmd) => {
                self.visit_node(**cmd);
            }
            Condition::ReturnZero(cmd) => self.visit_node(**cmd),
        }
    }

    /// Walk an arithmetic expression node.
    fn walk_arithmetic(&mut self, arith: &Arithmetic<String>) {
        use autotools_parser::ast::Arithmetic::*;
        match arith {
            UnaryPlus(x) | UnaryMinus(x) | LogicalNot(x) | BitwiseNot(x) => {
                self.visit_arithmetic(x)
            }
            Pow(x, y)
            | Mult(x, y)
            | Div(x, y)
            | Modulo(x, y)
            | Add(x, y)
            | Sub(x, y)
            | ShiftLeft(x, y)
            | ShiftRight(x, y)
            | Less(x, y)
            | LessEq(x, y)
            | Great(x, y)
            | GreatEq(x, y)
            | Eq(x, y)
            | NotEq(x, y)
            | BitwiseAnd(x, y)
            | BitwiseXor(x, y)
            | BitwiseOr(x, y)
            | LogicalAnd(x, y)
            | LogicalOr(x, y) => {
                self.visit_arithmetic(x);
                self.visit_arithmetic(y);
            }
            Ternary(x, y, z) => {
                self.visit_arithmetic(x);
                self.visit_arithmetic(y);
                self.visit_arithmetic(z);
            }
            Sequence(seq) => {
                for a in seq {
                    self.visit_arithmetic(a);
                }
            }
            _ => {}
        }
    }

    /// Walk a parameter node.
    fn walk_parameter(&mut self, _param: &Parameter<String>) {}

    /// Walk a parameter substitution node.
    fn walk_parameter_substitution(&mut self, subs: &ParameterSubstitution<AcWord>) {
        use autotools_parser::ast::ParameterSubstitution::*;
        match subs {
            Command(cmds) => {
                for c in cmds {
                    self.visit_node(*c);
                }
            }
            Arith(Some(arith)) => self.visit_arithmetic(arith),
            Len(param) => self.visit_parameter(param),
            Default(_, param, word)
            | Assign(_, param, word)
            | Error(_, param, word)
            | Alternative(_, param, word)
            | RemoveSmallestSuffix(param, word)
            | RemoveLargestSuffix(param, word)
            | RemoveSmallestPrefix(param, word)
            | RemoveLargestPrefix(param, word) => {
                self.visit_parameter(param);
                if let Some(w) = word {
                    self.visit_word(w);
                }
            }
            _ => {}
        }
    }

    /// Walk a function definition.
    fn walk_function_definition(&mut self, _name: &str, body: NodeId) {
        self.visit_node(body);
    }

    /// Walk an M4 macro node (walks arguments only).
    fn walk_m4_macro(&mut self, m4_macro: &M4Macro) {
        for arg in &m4_macro.args {
            match arg {
                M4Argument::Word(w) => self.visit_word(w),
                M4Argument::Array(ws) => {
                    for w in ws {
                        self.visit_word(w);
                    }
                }
                M4Argument::Condition(cond) => self.visit_condition(cond),
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

/// Represents a node extension in the dependency graph
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct NodeInfo {
    /// Index of the node in the original list
    pub node_id: NodeId,
    /// Node ID of the top-most parent node
    pub top_id: Option<NodeId>,
    /// ID of the chunk this node belongs to
    pub chunk_id: Option<ChunkId>,
    /// Exec ID representing execution order of the node.
    pub exec_id: ExecId,
    /// Exec ID at the exit of the node
    pub exit: ExecId,
    /// trailing comments
    // pub comment: Option<AcWord>,
    /// Range of line numbers where the body is effectively referenced.
    // pub ranges: Vec<(usize, usize)>,
    /// Body of commands referenced by this node.
    // pub cmd: AcCommand,
    /// Node ID of the parent node
    pub parent: Option<NodeId>,
    /// Block ID of the block where the node resides
    pub block: Option<BlockId>,
    /// Block IDs of the child branches
    /// The indexes correspond to the branch indexes of if/case statements
    pub branches: Vec<BlockId>,
    /// Optional Node ID for commands used in pre body clause.
    /// The reasons why we need this field instead of just creating
    /// a new block for the command are:
    /// 1. now we assume the indexes of child_blocks correspond to branch indexes
    /// 2. due to the parser's optimization, condtitions may not be represented as nodes but operators.
    /// FIXME: this looks dirty so refine it if possible.
    pub pre_body_nodes: Vec<NodeId>,
    /// Variables defined by this command
    pub definitions: VariableMap,
    /// Variables bounded by this command (items are duplicated with `definitions`)
    pub bounds: VariableMap,
    /// Variables defined by all children of this command
    pub propagated_definitions: VariableMap,
    /// Variables used by this command
    pub usages: VariableMap,
    /// Commands this command depends on by variables
    pub dependencies: NodeDependencyMap,
    /// Commands that depend on this node by variables
    pub dependents: NodeDependencyMap,
}

impl NodeInfo {
    pub fn is_top_node(&self) -> bool {
        self.top_id.is_some_and(|id| id == self.node_id)
    }

    pub fn is_child_node(&self) -> bool {
        self.parent.is_some()
    }
}

#[derive(Debug)]
struct AnalyzerOptions {
    flatten_threshold: usize,
}

impl Default for AnalyzerOptions {
    fn default() -> Self {
        Self {
            flatten_threshold: 200,
        }
    }
}

/// Analyzer which conducts various kinds of analyses:
/// 1. construction of a dependency graph by tracking variable usages
/// 2. flattening of large commands
/// etc..
#[derive(Debug, Default)]
pub struct Analyzer {
    /// Path to the analyzed script
    path: PathBuf,
    /// Original contents of analyzed script
    lines: Vec<String>,
    /// Nodes in the dependency graph
    pool: AutoconfPool<NodeInfo>,
    /// Ids of top-level commands
    top_ids: Vec<NodeId>,
    /// Map of block ID to Block information
    /// The node ids vector preserves the sequence order of commands.
    blocks: Slab<Block>,
    /// Chunks of nodes
    chunks: Slab<Chunk>,
    /// options of this analyzer
    options: AnalyzerOptions,
    /// Set of variable maps that is fixed to a certain value
    fixed: HashMap<String, String>,
    /// information about paths in the project
    project_info: ProjectInfo,
    /// information about platform support of Rust.
    platform_support: PlatformSupport,
    /// Analysis results of build options.
    build_option_info: BuildOptionInfo,
    /// Cache used inside Value Set Analysis. Mainly used for recording resolved values of variables
    vsa_cache: RefCell<VSACache>,
    /// Whether the nodes are flattened or not
    has_flattened_nodes: bool,
    /// Map of variable names to information of commands that define them
    var_definitions: Option<VariableMap>,
    /// Map of variable names to information of commands whose all children define them
    var_propagated_definitions: Option<VariableMap>,
    /// Map of variable names to information of commands that uses them
    var_usages: Option<VariableMap>,
    /// Map of variable names to information of commands that indirectly uses them
    var_indirect_usages: Option<VariableMap>,
    /// Set of variables which are used in eval assignments
    eval_assigns: Option<HashMap<Identifier, Vec<(Option<ValueExpr>, Location)>>>,
    /// dynamically divided identifiers
    /// The value of entry is a map from eval location to division info
    divided_vars: Option<HashMap<String, DividedVariable>>,
    /// all m4 macro calls
    macro_calls: Option<HashMap<String, Vec<(NodeId, M4Macro)>>>,
    /// prefix for all cpp symbol definitions
    cpp_prefix: Option<String>,
    /// all cpp symbol definitions
    cpp_defs: Option<HashSet<String>>,
    /// record side effects of fixed macros
    side_effects_of_frozen_macros: Option<HashMap<NodeId, FixedMacroSideEffect>>,
    /// conditional compilation map
    conditional_compilation_map: Option<ConditionalCompilationMap>,
    /// all susbstitued variables
    subst_vars: Option<HashSet<String>>,
    /// all input variables which are defined in m4 macros and are candidates of environmental variables.
    input_vars: Option<HashSet<String>>,
    /// all variables that can recieve user-supplied values other than build options.
    env_vars: Option<HashSet<String>>,
    /// Scopes of variables
    var_scopes: Option<HashMap<String, Vec<Scope>>>,
    /// Signatures of chunks as a function
    chunk_skeletons: Option<HashMap<ChunkId, FunctionSkelton>>,
    /// Inferred Types
    inferred_types: Option<HashMap<String, (HashSet<TypeHint>, DataType)>>,
    /// Dictionary Instances
    dicts: Option<Vec<DictionaryInstance>>,
    /// Analysis result of Automake files.
    automake: Option<AutomakeAnalyzer>,
}

#[allow(dead_code)]
impl Analyzer {
    /// Reorganize nodes to flatten deeply nested command blocks
    /// Note that once we call it, the structure of nodes will change irreversibly,
    /// which will affect behaviors of many analysis paths.
    pub fn flatten(&mut self) {
        Flattener::flatten(self, self.options.flatten_threshold);
        self.has_flattened_nodes = true;
    }

    /// Analyze commands and build the dependency graph
    pub fn new(path: &Path, flatten_threshold: Option<usize>) -> Self {
        let contents = if path.file_name().is_some_and(|os_str| {
            os_str
                .to_str()
                .is_some_and(|file_name| file_name == "configure.ac")
        }) {
            autotools_parser::preprocess::partial_expansion(path)
                .expect("Partial Expansion of configure.ac has failed.")
        } else {
            std::fs::read_to_string(path).expect("Reading a file has failed.")
        }
        // FIXME: We really don't want this variable. But the matching logic is incorrect
        // (e.g. $USER_VARIABLE -> SER_VARIABLE)
        .replace("$U", "");
        std::fs::read_to_string(&path).unwrap();
        // Move to the project directory
        let project_dir = path.parent().unwrap().to_owned();
        std::env::set_current_dir(&project_dir).expect("Unable to move to the project directory.");
        let fixed = [(
            "srcdir".to_owned(),
            ".".into(), // project_dir.to_str().unwrap().to_owned(),
        )];
        let lexer = Lexer::new(contents.chars());
        println!("==================== Parse BEGIN =======================");
        let (nodes, top_ids) = NodeParser::<_, NodeInfo>::new(lexer).parse_all();
        let nodes = nodes
            .into_iter()
            .map(|(node_id, mut n)| {
                n.info.node_id = node_id;
                (node_id, n)
            })
            .collect::<Slab<Node>>();

        let pool = AutoconfPool::new(nodes, Some(Box::new(|n| n.info.is_top_node())));
        println!("==================== Parse END =======================");

        let mut s = Self {
            path: path.to_owned(),
            lines: contents.lines().map(|s| s.to_string()).collect(),
            pool,
            top_ids,
            fixed: HashMap::from(fixed),
            options: AnalyzerOptions {
                flatten_threshold: flatten_threshold.unwrap_or(200),
            },
            project_info: ProjectInfo {
                project_dir,
                ..Default::default()
            },
            ..Default::default()
        };

        GuardAnalyzer::analyze_blocks(&mut s);

        s.filter_out_commands();

        println!("==================== M4 =======================");
        // Record all m4 macro calls
        s.find_macro_calls();

        // Create a VariableAnalyzer to extract both defined and used variables
        VariableAnalyzer::analyze_variables(&mut s);

        s.aggregate_def_use();

        println!("==================== VSA =======================");
        s.run_value_set_analysis();
        println!("==================== DICT =======================");
        s.run_type_inference();
        s.make_dictionary_instances();

        // analyze filesystem links
        s.analyze_link_macros();

        println!("==================== AUTOMAKE =======================");
        // Analyze automake files
        s.analyze_automake_files();
        s.aggregate_cpp_defs();
        s.aggregate_subst_vars();
        s.froze_macros();
        s.consume_automake_macros();

        s.load_project_files();
        println!("==================== CCP =======================");
        s.create_conditional_compilation_map();

        s.remove_unused_variables();

        s.run_build_option_analysis();

        // Flatten nodes
        s.flatten();

        s.aggregate_input_vars();

        // Construct chunks & cut var scopes
        s.construct_chunks(Some(2), false);
        s.cut_variable_scopes_chunkwise();

        s.aggregate_env_vars();

        s.construct_chunk_skeletons();

        s
    }

    /// Get guard conditions of given variable location
    fn guard_of_location(&self, location: &Location) -> Vec<Guard> {
        if let Some(block_id) = self.get_node(location.node_id).unwrap().info.block {
            self.blocks[block_id].guards.clone()
        } else if let Some(block_id) = self
            .get_parent(location.node_id)
            .and_then(|parent| self.get_node(parent).unwrap().info.block)
        {
            self.blocks[block_id].guards.clone()
        } else {
            Vec::new()
        }
    }

    fn get_branch_index(&self, parent_id: NodeId, block_id: BlockId) -> Option<usize> {
        self.get_node(parent_id)
            .unwrap()
            .info
            .branches
            .iter()
            .enumerate()
            .filter_map(|(index, bid)| (*bid == block_id).then_some(index))
            .next()
    }

    /// Get block ID of the block where the node resides
    fn block_of_node(&self, node_id: NodeId) -> Option<&Block> {
        if let Some(block_id) = self.get_node(node_id).unwrap().info.block {
            self.blocks.get(block_id)
        } else {
            None
        }
    }

    /// Get command that defines a variable before
    pub fn get_last_definition(&self, var_name: &str, node_id: NodeId) -> Option<NodeId> {
        if let Some(node) = self.pool.get(node_id) {
            if let Some(user_loc) = node.info.usages.get(var_name).map(|v| v.first()).flatten() {
                return self.get_definition(var_name).and_then(|v| {
                    v.iter()
                        .rev()
                        .filter_map(|loc| (loc <= user_loc).then_some(loc.node_id))
                        .next()
                });
            }
        }
        None
    }

    pub(crate) fn get_definition(&self, var_name: &str) -> Option<&Vec<Location>> {
        self.var_definitions.as_ref().unwrap().get(var_name)
    }

    pub(crate) fn has_definition(&self, var_name: &str) -> bool {
        self.var_definitions
            .as_ref()
            .unwrap()
            .contains_key(var_name)
    }

    pub(crate) fn has_definition_before(&self, var_name: &str, loc: &Location) -> bool {
        self.var_definitions
            .as_ref()
            .unwrap()
            .get(var_name)
            .is_some_and(|def_locs| def_locs.iter().any(|def_loc| def_loc < loc))
    }

    pub(crate) fn get_propagated_definition(&self, var_name: &str) -> Option<&Vec<Location>> {
        self.var_propagated_definitions
            .as_ref()
            .unwrap()
            .get(var_name)
    }

    pub(crate) fn as_propagated_definition(
        &self,
        var_name: &str,
        def_loc: &Location,
    ) -> Option<Location> {
        // we actually should save the information where the propagation comes from.
        // for now instead, we use this dumb logic.
        self.get_propagated_definition(var_name)
            .into_iter()
            .flat_map(|prop_def_locs| prop_def_locs.into_iter())
            .find(|prop_def| {
                self.collect_descendant_nodes_per_node(prop_def.node_id, false, true)
                    .contains(&def_loc.node_id)
            })
            .cloned()
    }

    pub(crate) fn has_propagated_definition(&self, var_name: &str) -> bool {
        self.var_propagated_definitions
            .as_ref()
            .unwrap()
            .contains_key(var_name)
    }

    pub(crate) fn get_usage(&self, var_name: &str) -> Option<&Vec<Location>> {
        self.var_usages.as_ref().unwrap().get(var_name)
    }

    pub(crate) fn has_usage(&self, var_name: &str) -> bool {
        self.var_usages.as_ref().unwrap().contains_key(var_name)
    }

    pub(crate) fn has_usage_before(&self, var_name: &str, loc: &Location) -> bool {
        self.var_usages
            .as_ref()
            .unwrap()
            .get(var_name)
            .is_some_and(|use_locs| use_locs.iter().any(|use_loc| use_loc < loc))
    }

    pub(crate) fn get_indirect_usage(&self, var_name: &str) -> Option<&Vec<Location>> {
        self.var_indirect_usages.as_ref().unwrap().get(var_name)
    }

    pub(crate) fn has_indirect_usage(&self, var_name: &str) -> bool {
        self.var_indirect_usages
            .as_ref()
            .unwrap()
            .contains_key(var_name)
    }

    pub(crate) fn is_substituted(&self, var_name: &str) -> bool {
        self.subst_vars.as_ref().unwrap().contains(var_name)
    }

    /// Get command that defines a variable before, with consideration for the condition
    pub fn get_dominant_definition(&self, var_name: &str, node_id: NodeId) -> Option<Location> {
        if let Some(node) = self.pool.get(node_id) {
            if let Some(use_loc) = node.info.usages.get(var_name).map(|v| v.first()).flatten() {
                let defs = self
                    .get_definition(var_name)
                    .into_iter()
                    .flat_map(|defs| defs.iter());

                let prop_defs = self
                    .get_propagated_definition(var_name)
                    .into_iter()
                    .flat_map(|defs| defs.iter())
                    .filter(|prop_def| {
                        // we should ignore propagation which may originate from the requested node itself.
                        !self
                            .collect_descendant_nodes_per_node(prop_def.node_id, false, true)
                            .contains(&node_id)
                    });

                return defs
                    .chain(prop_defs)
                    .sorted()
                    .rev()
                    .filter(|def_loc| def_loc <= &use_loc)
                    .filter(|def_loc| {
                        guard::cmp_guards(
                            &self.guard_of_location(def_loc),
                            &self.guard_of_location(use_loc),
                        )
                        .is_some_and(|ord| matches!(ord, Ordering::Less | Ordering::Equal))
                    })
                    .next()
                    .cloned();
            }
        }
        None
    }

    /// Get all locations that define a variable before
    pub fn get_all_definition(&self, var_name: &str, loc: Option<&Location>) -> Vec<Location> {
        self.get_definition(var_name)
            .into_iter()
            .flatten()
            .filter(|def_loc| loc.is_none() || loc.is_some_and(|loc| *def_loc < loc))
            .cloned()
            .collect::<Vec<_>>()
    }

    /// Get all locations that uses a variable
    pub fn get_all_usages(&self, var_name: &str, include_indirection: bool) -> Vec<Location> {
        self.get_all_usages_before(var_name, None, include_indirection)
    }

    /// Get all locations that uses a variable before
    pub fn get_all_usages_before(
        &self,
        var_name: &str,
        loc: Option<&Location>,
        include_indirection: bool,
    ) -> Vec<Location> {
        self.get_usage(var_name)
            .into_iter()
            .chain(
                include_indirection
                    .then_some(self.get_indirect_usage(var_name).into_iter())
                    .into_iter()
                    .flatten(),
            )
            .flatten()
            .filter(|use_loc| loc.is_none() || loc.is_some_and(|loc| *use_loc < loc))
            .cloned()
            .collect::<Vec<_>>()
    }

    /// Get all locations that uses a variable after
    pub fn get_all_usages_after(
        &self,
        var_name: &str,
        loc: Option<&Location>,
        include_indirection: bool,
    ) -> Vec<Location> {
        self.get_usage(var_name)
            .into_iter()
            .chain(
                include_indirection
                    .then_some(self.get_indirect_usage(var_name).into_iter())
                    .into_iter()
                    .flatten(),
            )
            .flatten()
            .filter(|use_loc| loc.is_none() || loc.is_some_and(|loc| *use_loc > loc))
            .cloned()
            .collect::<Vec<_>>()
    }

    /// Get all variables defined by a command
    pub fn get_defined_variables(&self, node_id: NodeId) -> Option<HashSet<String>> {
        self.pool
            .get(node_id)
            .map(|node| node.info.definitions.keys().cloned().collect())
    }

    /// Get all variables used by a command
    pub fn get_used_variables(&self, node_id: NodeId) -> Option<HashSet<String>> {
        self.pool
            .get(node_id)
            .map(|node| node.info.usages.keys().cloned().collect())
    }

    /// Get commands this node depends on
    pub fn get_dependencies(&self, node_id: NodeId) -> Option<HashMap<NodeId, HashSet<String>>> {
        self.pool
            .get(node_id)
            .map(|node| node.info.dependencies.clone())
    }

    /// Get commands that depend on this node
    pub fn get_dependents(&self, node_id: NodeId) -> Option<HashMap<NodeId, HashSet<String>>> {
        self.pool
            .get(node_id)
            .map(|node| node.info.dependencies.clone())
    }

    pub fn get_parent(&self, node_id: NodeId) -> Option<NodeId> {
        self.get_node(node_id).unwrap().info.parent
    }

    fn link_body_to_parent(&mut self, node_id: NodeId, parent: NodeId, block: BlockId) {
        self.get_node_mut(node_id).unwrap().info.parent = Some(parent);
        self.get_node_mut(node_id).unwrap().info.block = Some(block);
    }

    fn link_pre_body_to_parent(&mut self, node_id: NodeId, parent: NodeId) {
        self.get_node_mut(node_id).unwrap().info.parent = Some(parent);
    }

    pub fn get_children(&self, node_id: NodeId) -> Option<Vec<NodeId>> {
        let body_nodes = self.get_body(node_id).into_iter().flatten();

        let pre_body_nodes = self.pool.get(node_id).map_or_else(
            || [].iter().cloned(),
            |n| n.info.pre_body_nodes.iter().cloned(),
        );

        let children: Vec<_> = pre_body_nodes
            .chain(body_nodes)
            .filter(|id| self.node_exists(*id))
            .collect();

        (!children.is_empty()).then_some(children)
    }

    pub fn get_body(&self, node_id: NodeId) -> Option<Vec<NodeId>> {
        self.pool.get(node_id).and_then(|n| {
            if n.info.branches.is_empty() {
                None
            } else {
                Some(
                    n.info
                        .branches
                        .iter()
                        .map(|block_id| {
                            self.blocks
                                .get(*block_id)
                                .map(|block| block.nodes.clone().into_iter())
                        })
                        .flatten()
                        .flatten()
                        .filter(|id| self.node_exists(*id))
                        .collect(),
                )
            }
        })
    }

    /// Get vector of all node ids
    pub fn get_ids(&self) -> Vec<NodeId> {
        self.pool.nodes.iter().map(|(id, _)| id).collect()
    }

    /// Get vector of all ids of top-level nodes
    pub fn get_top_ids(&self) -> Vec<NodeId> {
        self.top_ids.clone()
    }

    /// Get a range of the command at the specified index
    pub fn get_ranges(&self, id: NodeId) -> Option<&[(usize, usize)]> {
        self.pool.get(id).map(|n| n.range.as_ref())
    }
    /// Get a reference to the command at the specified index
    pub fn get_command(&self, id: NodeId) -> Option<&AcCommand> {
        self.pool.nodes.get(id).map(|n| &n.cmd)
    }

    /// Get all commands that define or use a variable
    pub fn find_commands_with_variable(&self, var_name: &str) -> HashSet<NodeId> {
        let mut result = HashSet::new();

        // Add commands that define the variable
        if let Some(defs) = self.get_definition(var_name) {
            result.extend(defs.iter().map(|loc| loc.node_id));
        }

        // Add commands that use the variable
        for (id, node) in &self.pool.nodes {
            if node.info.usages.contains_key(var_name) {
                result.insert(id);
            }
        }

        result
    }

    /// Check if the node exists
    pub fn node_exists(&self, node_id: NodeId) -> bool {
        self.pool.nodes.contains(node_id)
    }

    /// Get node representation by id
    pub fn get_node(&self, node_id: NodeId) -> Option<&Node> {
        self.pool.nodes.get(node_id)
    }

    /// Get node representation by id
    pub fn get_node_mut(&mut self, node_id: NodeId) -> Option<&mut Node> {
        self.pool.nodes.get_mut(node_id)
    }

    fn get_block(&self, block_id: BlockId) -> &Block {
        &self.blocks[block_id]
    }

    fn get_block_mut(&mut self, block_id: BlockId) -> &mut Block {
        &mut self.blocks[block_id]
    }

    /// Get original content of commands in specified node
    pub fn get_content(&self, node_id: NodeId) -> Option<Vec<String>> {
        self.pool.get(node_id).map(|node| {
            node.range
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
    pub fn display_node(&self, node_id: NodeId) -> String {
        self.pool.display_node(node_id, 0)
    }

    /// Recover the content of words from the AST structure
    pub fn display_word(&self, word: &AcWord) -> String {
        self.pool.display_word(word, false)
    }

    fn add_block(&mut self, block: Block) -> BlockId {
        let new_id = self.blocks.insert(block);
        self.get_block_mut(new_id).block_id = new_id;
        new_id
    }

    fn add_pre_body_node(&mut self, parent: NodeId, pre_body_node_id: NodeId) {
        self.get_node_mut(parent)
            .unwrap()
            .info
            .pre_body_nodes
            .push(pre_body_node_id);
        self.link_pre_body_to_parent(pre_body_node_id, parent);
    }

    fn collect_descendant_nodes_per_node(
        &self,
        node_id: NodeId,
        aware_chunk_boundary: bool,
        include_pre_body_nodes: bool,
    ) -> Vec<NodeId> {
        let mut stack = vec![node_id];
        let mut ret = HashSet::new();
        while let Some(id) = stack.pop() {
            if !ret.contains(&id) {
                ret.insert(id);
                if let Some(children) = if include_pre_body_nodes {
                    self.get_children(id)
                } else {
                    self.get_body(id)
                } {
                    let filtered = children.iter().filter(|&&child| {
                        // if aware chunk boundary,
                        // exclude children that are beyond chunk boundary
                        !(aware_chunk_boundary && self.get_node(child).unwrap().info.is_top_node())
                    });
                    stack.extend(filtered.clone());
                }
            }
        }
        ret.into_iter()
            .sorted_by_key(|id| self.get_node(*id).unwrap().info.exec_id)
            .collect()
    }

    /// recursively collect defined/used variables
    pub(crate) fn collect_dependencies(
        &self,
        node_id: NodeId,
    ) -> (NodeDependencyMap, NodeDependencyMap) {
        let mut dependencies = HashMap::new();
        let mut dependents = HashMap::new();
        for id in self.collect_descendant_nodes_per_node(node_id, false, false) {
            if let Some(node) = self.pool.nodes.get(id) {
                dependencies.extend(node.info.dependencies.clone().into_iter());
                dependents.extend(node.info.dependents.clone().into_iter());
            }
        }
        (dependencies, dependents)
    }

    fn is_var_used(&self, var_name: &str) -> bool {
        self.has_usage(var_name)
            || self.has_indirect_usage(var_name)
            || self.is_substituted(var_name)
    }

    /// recursively collect defined/used variables
    pub(crate) fn collect_variables(&self, node_id: NodeId) -> (VariableMap, VariableMap) {
        let mut defines = HashMap::new();
        let mut uses = HashMap::new();
        for id in self.collect_descendant_nodes_per_node(node_id, true, false) {
            if let Some(node) = self.get_node(id) {
                let new_defines = node
                    .info
                    .definitions
                    .iter()
                    .filter_map(|(s, v)| self.is_var_used(s).then_some((s.clone(), v.clone())));
                self.extend_var_maps(&mut defines, new_defines);

                let new_uses = node.info.usages.iter().map(|(s, v)| (s.clone(), v.clone()));
                self.extend_var_maps(&mut uses, new_uses);
            }
        }
        (defines, uses)
    }

    pub(crate) fn apply_def_use_edges(&mut self, def_use_edges: Vec<(NodeId, NodeId, String)>) {
        // Apply initialization of depdencies to nodes
        for (def_id, use_id, var_name) in def_use_edges {
            self.get_node_mut(use_id)
                .unwrap()
                .info
                .dependencies
                .entry(def_id)
                .or_default()
                .insert(var_name.to_owned());
            self.get_node_mut(def_id)
                .unwrap()
                .info
                .dependents
                .entry(use_id)
                .or_default()
                .insert(var_name.to_owned());
        }
    }

    pub(crate) fn extend_var_maps<I>(&self, var_map: &mut VariableMap, new_items: I)
    where
        I: Iterator<Item = (String, Vec<Location>)>,
    {
        for (k, v) in new_items {
            var_map
                .entry(k)
                .and_modify(|locs| locs.extend(v.clone()))
                .or_insert(v);
        }
    }

    pub(crate) fn print_entire_scripts(&self) -> String {
        self.get_top_ids()
            .into_iter()
            .map(|id| self.display_node(id))
            .join("\n")
    }
}
