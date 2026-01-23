use std::{
    cell::{Cell, RefCell},
    collections::HashMap,
};

/// Placeholder format for heredoc content.
/// The format is "__HEREDOC_<index>__" followed by " {}" for each variable.
const HEREDOC_PLACEHOLDER_PREFIX: &str = "__HEREDOC_";

use super::InlinedTranslationOutput;
use crate::analyzer::{
    as_literal, as_shell, as_single,
    build_option::FeatureState,
    chunk::ChunkId,
    conditional_compilation::CCMigrationType,
    dictionary::{DictionaryAccess, DictionaryOperation, DictionaryValue},
    guard::{Atom, VarCond, VoL},
    location::Location,
    translator::{
        pretranslation::{self, get_function_body_ac_init, get_function_body_am_init_automake},
        InlineEvidence,
    },
    type_inference::DataType,
    variable::is_eval,
    Analyzer, BlockId, Guard, NodeInfo,
};
use autotools_parser::{
    ast::{
        minimal::Word,
        node::{
            AcCommand, AcWord, AcWordFragment, Condition, DisplayM4, DisplayNode, GuardBodyPair,
            M4Macro, Node, NodeId, NodePool, ParameterSubstitution, PatternBodyPair, WordFragment,
        },
        Arithmetic, MayM4, Parameter, Redirect,
    },
    m4_macro::{M4Argument, VarUsage},
};

use itertools::Itertools;

#[derive(Debug, Clone, Default)]
pub(super) struct FuncRequests {
    /// Whether we have found a usage of redirection.
    found_redirection: bool,
    /// Whether we have found a usage of sed command.
    found_sed: bool,
    /// Whether we have found a usage of define_cfg/define_env
    found_define: bool,
    /// Whether we have found a usage of pkg_config
    found_pkg_config: bool,
    /// Whether we have found a usage of AC_CHECK_HEADER/AC_CHECK_HEADERS
    found_check_header: bool,
    /// Whether we have found a usage of AC_CHECK_LIB/AC_SEARCH_LIBS
    found_check_library: bool,
    /// Whether we have found a usage of AC_CHECK_DECL/AC_CHECK_DECLS
    found_check_decl: bool,
    /// Whether we have found a usage of AC_CHECK_FUNC/AC_CHECK_FUNCS
    found_check_func: bool,
    /// Whether we have found a usage of AC_COMPILE_IFELSE/AC_TRY_COMPILE
    found_check_compile: bool,
    /// Whether we have found a usage of AC_LINK_IFELSE/AC_TRY_LINK
    found_check_link: bool,
}

impl FuncRequests {
    pub fn merge(&mut self, other: Self) {
        self.found_redirection |= other.found_redirection;
        self.found_sed |= other.found_sed;
        self.found_redirection |= other.found_redirection;
        self.found_sed |= other.found_sed;
        self.found_define |= other.found_define;
        self.found_pkg_config |= other.found_pkg_config;
        self.found_check_header |= other.found_check_header;
        self.found_check_library |= other.found_check_library;
        self.found_check_decl |= other.found_check_decl;
        self.found_check_func |= other.found_check_func;
        self.found_check_compile |= other.found_check_compile;
        self.found_check_link |= other.found_check_link;
    }
}

pub(crate) struct TranslatingPrinter<'a> {
    /// Contains all stateful information
    analyzer: &'a Analyzer,
    /// Assigned the id of top-most node while formatting a tree of nodes.
    current_top_most: Cell<Option<NodeId>>,
    /// Current ID of the node to be displayed.
    node_cursor: Cell<Option<NodeId>>,
    /// Current index of the branch to be displayed.
    branch_cursor: Cell<Option<BlockId>>,
    /// The order in expression to reproduce precise Location.
    order: Cell<usize>,
    /// Whether we assume that we can and will translate all nodes to rust.
    full_rust_mode: bool,
    /// Nodes that should be translated as dictionary accesses.
    dict_accesses: HashMap<Location, (String, DictionaryAccess, DataType)>,
    /// Fragments that are translated while printing.
    required_snippets: RefCell<Vec<String>>,
    /// Max number of consecutive slashes apeared in translated fragments.
    max_num_consecutive_slashes: Cell<Option<usize>>,
    /// Whether parameters are to be displayed in the style of rust's format string
    in_format_string: Cell<bool>,
    /// When `in_format_string` is set to true, we record appeared variables here.
    formatted_vars: RefCell<Vec<String>>,
    /// Whether are we printing an assignment.
    in_literal_assignment: Cell<bool>,
    /// When `in_literal_assignment` is set to true, we record appeared literals here.
    assigned_literals: RefCell<Vec<String>>,
    /// Appeared chunks when embedding
    embedded_chunks: RefCell<HashMap<ChunkId, String>>,
    /// Appeared features
    cargo_features: RefCell<Vec<String>>,
    /// Called m4 macros to be expanded in configure.
    called_macros: RefCell<Vec<String>>,
    /// Simple translations available for inlining
    inlined_translations: Option<&'a HashMap<ChunkId, InlinedTranslationOutput>>,
    /// keys for required funcs
    func_requests: RefCell<FuncRequests>,
    /// Heredoc placeholders: (placeholder_format, original_format)
    heredoc_placeholders: RefCell<Vec<(String, String)>>,
    /// Counter for generating unique heredoc placeholder IDs
    heredoc_counter: Cell<usize>,
}

impl<'a> std::fmt::Debug for TranslatingPrinter<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Printer")
            .field("forcus", &self.current_top_most)
            .finish()
    }
}

impl<'a> TranslatingPrinter<'a> {
    /// Construct a new printer with inlined translations for inlining
    pub fn new(
        analyzer: &'a Analyzer,
        inlined_translations: Option<&'a HashMap<ChunkId, InlinedTranslationOutput>>,
        full_rust_mode: bool,
    ) -> Self {
        let mut dict_accesses = HashMap::new();
        for dict in analyzer.dicts() {
            for (loc, access) in dict.accesses.iter() {
                dict_accesses.insert(
                    loc.clone(),
                    (dict.name.clone(), access.clone(), dict.value_type.clone()),
                );
            }
        }
        // FIXME: we have to use bunch of `Cell` to mutate the fields because of
        // the trait NodePool defined in autoconf_parser. But we could fix this trait
        // to allow all mutation.
        Self {
            analyzer,
            current_top_most: Cell::new(None),
            node_cursor: Cell::new(None),
            branch_cursor: Cell::new(None),
            order: Cell::new(0),
            full_rust_mode,
            dict_accesses,
            required_snippets: RefCell::new(Vec::new()),
            max_num_consecutive_slashes: Cell::new(None),
            in_format_string: Cell::new(false),
            formatted_vars: RefCell::new(Vec::new()),
            in_literal_assignment: Cell::new(false),
            assigned_literals: RefCell::new(Vec::new()),
            embedded_chunks: RefCell::new(HashMap::new()),
            cargo_features: RefCell::new(Vec::new()),
            called_macros: RefCell::new(Vec::new()),
            inlined_translations,
            func_requests: RefCell::new(FuncRequests::default()),
            heredoc_placeholders: RefCell::new(Vec::new()),
            heredoc_counter: Cell::new(0),
        }
    }

    pub fn get_node(&self, node_id: NodeId) -> Option<&Node<AcCommand, NodeInfo>> {
        self.analyzer.get_node(node_id)
    }

    pub fn print_node(&self, node_id: NodeId) -> String {
        self.current_top_most.replace(Some(node_id));
        let ret = self.display_node(node_id, 0);
        self.current_top_most.replace(None);
        ret
    }

    pub fn require_snippet(&self, frag: String) {
        // won't check too long fragments
        let mut v = self.required_snippets.borrow_mut();
        if !v.contains(&frag) {
            v.push(frag);
        }
    }

    pub fn get_required_snippets(&self) -> Vec<String> {
        self.required_snippets.borrow().clone()
    }

    pub fn get_func_requests(&self) -> FuncRequests {
        self.func_requests.borrow().clone()
    }

    pub fn get_max_num_consecutive_slashes(&self) -> Option<usize> {
        self.max_num_consecutive_slashes.get()
    }

    pub fn get_cargo_features(&self) -> Vec<String> {
        self.cargo_features
            .borrow()
            .clone()
            .into_iter()
            .dedup()
            .collect()
    }

    /// Create a heredoc placeholder and store the mapping.
    /// Returns the placeholder format string (e.g., "__HEREDOC_0__" or "__HEREDOC_0__ {} {}").
    fn create_heredoc_placeholder(&self, original_format: String, num_vars: usize) -> String {
        let index = self.heredoc_counter.get();
        self.heredoc_counter.set(index + 1);
        let placeholder_suffix = " {}".repeat(num_vars);
        let placeholder_format = format!(
            "{}{}__{}",
            HEREDOC_PLACEHOLDER_PREFIX, index, placeholder_suffix
        );
        self.heredoc_placeholders
            .borrow_mut()
            .push((placeholder_format.clone(), original_format));
        placeholder_format
    }

    /// Get the collected heredoc placeholders: (placeholder_format, original_format)
    pub fn get_heredoc_placeholders(&self) -> Vec<(String, String)> {
        self.heredoc_placeholders.borrow().clone()
    }

    fn enclose_by_rust_tags(&self, fragment: String, require: bool) -> String {
        if self.full_rust_mode {
            // early return
            return fragment;
        }

        if require {
            self.require_snippet(fragment.clone());
        }
        format!("<rust>{}</rust>", fragment)
    }

    pub fn get_banned_patterns(&self) -> Vec<(String, String)> {
        let mut ret = Vec::new();
        if self.func_requests.borrow().found_sed {
            // regex syntax b/w sed (bre/ere) and rust (re2) are not compatible.
            // Especially when we allow LLMs to use multi-line mode: (?m), they often fail to
            // correctly migrate regex patterns.
            // So we decided to simply ban the mode and instruct them to do line-by-line instead.
            ret.push((
                "(?m)".into(),
                "When using regex, multi-line mode is prohibited.".into(),
            ));
        }
        for macro_name in self.called_macros.borrow().iter() {
            ret.push((
                macro_name.clone(),
                "You must appropriately translate this macro call.".into(),
            ))
        }
        ret
    }

    pub fn get_rust_funcs_required_for_chunk(&self) -> Vec<String> {
        let mut ret = Vec::new();
        let requests = self.func_requests.borrow();
        // module imports
        // if requests.found_sed {
        //     ret.push("module_regex");
        // }
        if requests.found_pkg_config {
            ret.push("module_pkg_config");
        }
        // function definitions
        if requests.found_redirection {
            ret.push("write_file");
        }
        if requests.found_define {
            ret.push("define_cfg");
            ret.push("define_env");
        }
        if requests.found_pkg_config {
            ret.push("pkg_config");
        }
        if requests.found_check_header {
            ret.push("check_header");
        }
        if requests.found_check_library {
            ret.push("check_library");
        }
        if requests.found_check_decl {
            ret.push("check_decl");
        }
        if requests.found_check_func {
            ret.push("check_func");
        }
        if requests.found_check_compile {
            ret.push("check_compile");
        }
        if requests.found_check_link {
            ret.push("check_link");
        }
        ret.into_iter().map(|s| s.to_owned()).collect()
    }

    pub fn get_embedded_chunks(&self) -> HashMap<ChunkId, String> {
        self.embedded_chunks.borrow().clone()
    }

    /// Get the chunk ID for the current node cursor position
    fn get_current_chunk_id(&self) -> Option<ChunkId> {
        self.node_cursor
            .get()
            .and_then(|node_id| self.analyzer.get_chunk_id(node_id))
    }

    pub fn get_tab_width() -> usize {
        Self::TAB_WIDTH
    }

    fn propagate_inlined_evidence(&self, evidence: Option<InlineEvidence>) {
        if let Some(e) = evidence {
            self.required_snippets
                .borrow_mut()
                .extend(e.required_snippets);
            self.func_requests.borrow_mut().merge(e.func_requests);
            self.cargo_features.borrow_mut().extend(e.features);
            self.heredoc_placeholders
                .borrow_mut()
                .extend(e.placeholders);
        }
    }
}

impl<'a> DisplayNode for TranslatingPrinter<'a> {
    type Word = AcWord;

    fn display_node(&self, node_id: NodeId, indent_level: usize) -> String {
        if let Some(node) = self.get_node(node_id) {
            let is_top_most = self.current_top_most.get().unwrap() == node_id;
            if !is_top_most && node.info.is_chunk_top_node() {
                // "is_chunk_top == false" and here the node says it's top node.
                // -> Found node beyond chunk boundary
                let chunk_id = node.info.chunk_id.unwrap();
                if self.embedded_chunks.borrow().contains_key(&chunk_id) {
                    return "".into();
                } else {
                    let tab = " ".repeat(indent_level * Self::TAB_WIDTH);

                    // Check if we have a inlined translation for this chunk
                    if let Some(inlined_translation) = self
                        .inlined_translations
                        .as_ref()
                        .and_then(|m| m.get(&chunk_id))
                    {
                        // Inline the inlined translation directly
                        self.embedded_chunks
                            .borrow_mut()
                            .insert(chunk_id, "inlined".to_string());

                        let inlined_code = inlined_translation
                            .inline_rust_code
                            .iter()
                            .filter(|line| !line.is_empty())
                            .map(|line| {
                                format!("{tab}{}", self.enclose_by_rust_tags(line.clone(), false))
                            })
                            .collect::<Vec<_>>()
                            .join("\n");
                        self.propagate_inlined_evidence(inlined_translation.evidence.clone());
                        return inlined_code.to_string();
                    } else {
                        // function call for LLM-translated chunks
                        let func_name = super::rust_func_placeholder_name(chunk_id);
                        self.embedded_chunks
                            .borrow_mut()
                            .insert(chunk_id, func_name.clone());

                        let caller_chunk_id = self
                            .node_cursor
                            .get()
                            .and_then(|nid| self.get_node(nid))
                            .and_then(|node| node.info.chunk_id);
                        let call_site = self.analyzer.print_chunk_skeleton_call_site(
                            caller_chunk_id,
                            chunk_id,
                            &func_name,
                        );
                        return format!("{tab}{}", self.enclose_by_rust_tags(call_site, false));
                    }
                }
            }
            let saved_node_cursor = self.node_cursor.replace(Some(node_id));
            let saved_branch_cursor = self.branch_cursor.replace(None);
            let saved_order = self.set_order(0);
            use MayM4::*;
            let result = match &node.cmd.0 {
                Macro(m4_macro) => self.display_m4_macro(m4_macro, indent_level),
                Shell(cmd) => self.display_command(cmd, node.comment.clone(), indent_level),
            };
            self.set_order(saved_order);
            self.branch_cursor.replace(saved_branch_cursor);
            self.node_cursor.replace(saved_node_cursor);
            result
        } else {
            String::new()
        }
    }

    fn display_word(&self, word: &AcWord, should_quote: bool) -> String {
        use autotools_parser::ast::minimal::Word::*;
        use autotools_parser::ast::minimal::WordFragment::{DoubleQuoted, Literal};
        match &word.0 {
            Empty => {
                if should_quote {
                    "\"\"".to_string()
                } else {
                    String::new()
                }
            }
            Concat(frags) => frags
                .iter()
                .map(|w| self.display_may_m4_word(w))
                .collect::<Vec<String>>()
                .concat()
                .to_string(),
            Single(frag) => {
                let s = self.display_may_m4_word(frag);
                if should_quote {
                    match frag {
                        MayM4::Shell(Literal(lit)) if !lit.contains("\'") => {
                            format!("\'{}\'", s)
                        }
                        MayM4::Shell(DoubleQuoted(_)) => s,
                        _ => {
                            format!("\"{}\"", s)
                        }
                    }
                } else {
                    s
                }
            }
        }
    }
}

impl<'a> TranslatingPrinter<'a> {
    fn set_order(&self, order: usize) -> usize {
        self.order.replace(order)
    }

    fn increment_order(&self) {
        self.order.replace(self.order.get() + 1);
    }

    fn take_location(&self) -> Location {
        let node_id = self.node_cursor.get().unwrap();
        let node = self.analyzer.get_node(node_id).unwrap();
        let exec_id = node.info.exec_id;
        let line = node.range_start().unwrap();
        let order_in_expr = self.order.get();
        let loc = Location {
            node_id,
            exec_id,
            line,
            order_in_expr,
        };
        self.increment_order();
        loc
    }

    fn display_dictionary_value(&self, val: &DictionaryValue) -> String {
        match val {
            DictionaryValue::Lit(lit) => lit.into(),
            DictionaryValue::Var(name, _) => format!("${{{}}}", name),
            DictionaryValue::Dict(_, loc) => {
                let (dict_name, access, value_type) = self.dict_accesses.get(loc).unwrap();
                self.display_dictionary_read(dict_name, access, value_type)
            }
        }
    }

    fn display_dictionary_read(
        &self,
        dict_name: &str,
        access: &DictionaryAccess,
        _value_type: &DataType,
    ) -> String {
        debug_assert_eq!(access.operation, DictionaryOperation::Read);
        let keys = access
            .keys
            .iter()
            .map(|key| key.print())
            .collect::<Vec<_>>();
        let num_keys = keys.len();
        let operation = match num_keys {
            1 => {
                let key = keys.first().unwrap();
                let is_reference = self
                    .get_current_chunk_id()
                    .and_then(|cid| self.analyzer.chunk_skeletons().get(&cid))
                    .is_some_and(|sk| {
                        sk.args.contains_key(key)
                            || sk.pass_through_args.contains_key(key)
                            || sk.pass_through_maps.contains_key(key)
                            || sk.bound_in_loop.contains_key(key)
                    });
                let printed_keys = if is_reference {
                    key.clone()
                } else {
                    format!("&{}", key)
                };
                format!("{}.get({})", dict_name, printed_keys)
            }
            _ => {
                let printed_keys = format!(
                    "({})",
                    keys.into_iter()
                        .map(|key| format!("{}.to_string()", key))
                        .join(", ")
                );
                format!("{}.get(&{})", dict_name, printed_keys)
            }
        };
        operation
    }

    /// Translates a DictionaryValue into Rust code for use in value expressions.
    fn display_dictionary_value_as_rust(&self, val: &DictionaryValue) -> String {
        match val {
            DictionaryValue::Lit(lit) => format!("\"{}\".to_string()", lit),
            DictionaryValue::Var(name, _) => format!("${{{}}}", name),
            DictionaryValue::Dict(_, loc) => {
                let (dict_name, access, value_type) = self.dict_accesses.get(loc).unwrap();
                format!(
                    "{}.cloned().unwrap_or_default().into_iter()",
                    self.display_dictionary_read(dict_name, access, value_type)
                )
            }
        }
    }

    fn display_dictionary_write(
        &self,
        dict_name: &str,
        access: &DictionaryAccess,
        value_type: &DataType,
        value: Option<&str>,
    ) -> String {
        debug_assert_eq!(access.operation, DictionaryOperation::Write);
        let keys = access
            .keys
            .iter()
            .map(|key| key.print())
            .collect::<Vec<_>>();
        let num_keys = keys.len();
        let printed_keys = match num_keys {
            1 => format!("{}.to_string()", keys.first().unwrap()),
            _ => format!(
                "({})",
                keys.into_iter()
                    .map(|key| format!("{}.to_string()", key))
                    .join(", ")
            ),
        };

        self.require_snippet(dict_name.to_owned());
        self.require_snippet(printed_keys.to_owned());

        match value_type {
            DataType::List(_) => {
                // For List types, use assigned_value to generate proper Rust code
                if let Some(assigned_values) = &access.assigned_value {
                    let has_dict_values = assigned_values.iter().any(|v| {
                        if let DictionaryValue::Dict(_name, loc) = v {
                            self.dict_accesses.contains_key(loc)
                        } else {
                            false
                        }
                    });

                    if has_dict_values {
                        // Pattern B: Appending to existing values using entry().extend()
                        let mut dict_iters = Vec::new();
                        let mut non_dict_values = Vec::new();

                        for val in assigned_values {
                            match val {
                                DictionaryValue::Dict(_, loc) => {
                                    let (d_name, d_access, d_type) =
                                        self.dict_accesses.get(loc).unwrap();
                                    dict_iters.push(format!(
                                        "{}.cloned().unwrap_or_default().into_iter()",
                                        self.display_dictionary_read(d_name, d_access, d_type)
                                    ));
                                }
                                DictionaryValue::Lit(lit) => {
                                    non_dict_values.push(format!("\"{}\".to_string()", lit));
                                }
                                DictionaryValue::Var(name, _) => {
                                    non_dict_values.push(format!("${{{}}}", name));
                                }
                            }
                        }

                        let chain_parts: Vec<String> = dict_iters
                            .into_iter()
                            .chain(if non_dict_values.is_empty() {
                                None
                            } else {
                                Some(format!("[{}]", non_dict_values.join(", ")))
                            })
                            .collect();

                        let extend_expr = chain_parts.join(".chain(")
                            + &")".repeat(chain_parts.len().saturating_sub(1));
                        let operation = format!(
                            "{}.entry({}).or_default().extend({})",
                            dict_name, printed_keys, extend_expr
                        );
                        self.enclose_by_rust_tags(operation, false)
                    } else {
                        // Pattern A: Fresh assignment using insert() with vec![]
                        let values: Vec<String> = assigned_values
                            .iter()
                            .map(|v| self.display_dictionary_value_as_rust(v))
                            .collect();
                        let operation = format!(
                            "{}.insert({}, vec![{}])",
                            dict_name,
                            printed_keys,
                            values.join(", ")
                        );
                        self.enclose_by_rust_tags(operation, false)
                    }
                } else if let Some(val) = value {
                    // Fallback: use provided value string (for display_assignment case)
                    let lhs = self.enclose_by_rust_tags(
                        format!("{}.entry({})", dict_name, printed_keys),
                        false,
                    );
                    format!("{}=\"{}\"", lhs, val)
                } else {
                    // No value available
                    self.enclose_by_rust_tags(
                        format!("{}.entry({}).or_default()", dict_name, printed_keys),
                        false,
                    )
                }
            }
            _ => {
                // Non-list types: use simple insert
                let lhs = self
                    .enclose_by_rust_tags(format!("{}.insert({},", dict_name, printed_keys), false);
                let rhs = value.map(|v| v.to_owned()).unwrap_or_else(|| {
                    access
                        .assigned_value
                        .as_ref()
                        .map(|vals| {
                            vals.iter()
                                .map(|v| self.display_dictionary_value(v))
                                .join(" ")
                        })
                        .unwrap_or_default()
                });
                format!("{}=\"{}\"", lhs, rhs)
            }
        }
    }

    fn display_atom_as_cfg(&self, atom: &Atom, negated: bool) -> String {
        use Atom::*;
        let as_feature = |feature: &str| {
            self.cargo_features.borrow_mut().push(feature.into());
            format!("feature = \"{}\"", feature)
        };
        let may_negate = |str: String, negated: bool| {
            if negated {
                format!("not({})", str)
            } else {
                str
            }
        };
        match atom {
            Arch(arch) => may_negate(format!("target_arch = \"{}\"", arch), negated),
            Cpu(_) => todo!(),
            Os(os) => may_negate(format!("target_os = \"{}\"", os), negated),
            Env(env) => may_negate(format!("target_env = \"{}\"", env), negated),
            Abi(abi) => may_negate(format!("target_abi = \"{}\"", abi), negated),
            Arg(name, var_cond) => {
                let option_name = self
                    .analyzer
                    .build_option_info()
                    .arg_var_to_option_name
                    .get(name)
                    .unwrap_or(name);
                let find_feature = |value: &str| -> Option<(&str, &FeatureState)> {
                    self.analyzer
                        .build_option_info()
                        .cargo_features
                        .as_ref()
                        .and_then(|cargo_features| {
                            cargo_features
                                .get(option_name.as_str())
                                .and_then(|features| {
                                    features.iter().find_map(|feature| {
                                        feature.value_map.get(value).map(|feature_state| {
                                            (feature.name.as_str(), feature_state)
                                        })
                                    })
                                })
                        })
                };
                match var_cond {
                    VarCond::True => {
                        if let Some((feature_name, feature_state)) = find_feature("yes") {
                            let negated = feature_state.is_negative() ^ negated;
                            may_negate(as_feature(feature_name), negated)
                        } else {
                            // fallback
                            let key = self
                                .analyzer
                                .query_conditional_compilation_migration_policy(option_name)
                                .and_then(|policy| policy.key.as_ref())
                                .unwrap_or(option_name);
                            may_negate(key.into(), false ^ negated)
                        }
                    }
                    VarCond::False => {
                        if let Some((feature_name, feature_state)) = find_feature("no") {
                            let negated = feature_state.is_negative() ^ negated;
                            may_negate(as_feature(feature_name), negated)
                        } else {
                            // fallback
                            let key = self
                                .analyzer
                                .query_conditional_compilation_migration_policy(option_name)
                                .and_then(|policy| policy.key.as_ref())
                                .unwrap_or(option_name);
                            may_negate(key.into(), true ^ negated)
                        }
                    }
                    VarCond::Eq(VoL::Lit(lit)) => {
                        if let Some((feature_name, feature_state)) = find_feature(lit) {
                            let negated = feature_state.is_negative() ^ negated;
                            may_negate(as_feature(feature_name), negated)
                        } else {
                            // fallback
                            let key = self
                                .analyzer
                                .query_conditional_compilation_migration_policy(option_name)
                                .and_then(|policy| policy.key.as_ref())
                                .unwrap_or(option_name);
                            may_negate(format!("{}_{}", key, lit), false ^ negated)
                        }
                    }
                    _ => {
                        todo!("Printing Arg({}, {:?})", name, var_cond);
                    }
                }
            }
            Cmd(cmd) => {
                todo!("Cmd {}: {:?}", cmd, self.display_node(*cmd, 0));
            }
            _ => {
                todo!("{:?}", atom);
            }
        }
    }

    fn display_atom_as_optional(&self, atom: &Atom, negated: bool) -> String {
        use Atom::*;
        match atom {
            Var(name, var_cond) => {
                let is_set = match var_cond {
                    VarCond::Set => negated ^ true,
                    VarCond::False => negated ^ false,
                    _ => unreachable!(),
                };
                if is_set {
                    format!("{}.is_some()", name)
                } else {
                    format!("{}.is_none()", name)
                }
            }
            _ => {
                unreachable!()
            }
        }
    }

    fn display_var_atom(&self, atom: &Atom, negated: bool) -> String {
        use Atom::*;
        let may_negate = |str: String, negated: bool| {
            if negated {
                format!("!{}", str)
            } else {
                str
            }
        };
        match atom {
            Var(name, var_cond) => match var_cond {
                VarCond::True => {
                    let negated = false ^ negated;
                    match self.analyzer.get_data_type(name) {
                        DataType::Boolean => may_negate(name.into(), negated),
                        DataType::Literal => {
                            format!("{name} {} \"yes\"", if negated { "!=" } else { "==" })
                        }
                        DataType::List(_) => may_negate(format!("{name}.is_empty()"), !negated),
                        _ => todo!(),
                    }
                }
                VarCond::False => {
                    let negated = true ^ negated;
                    match self.analyzer.get_data_type(name) {
                        DataType::Boolean => may_negate(name.into(), negated),
                        DataType::Literal => {
                            format!("{name} {} \"no\"", if negated { "!=" } else { "==" })
                        }
                        DataType::List(_) => may_negate(format!("{name}.is_empty()"), !negated),
                        _ => todo!(),
                    }
                }
                VarCond::Eq(VoL::Lit(lit)) => {
                    may_negate(format!("({} == \"{}\")", name, lit), false ^ negated)
                }
                VarCond::Eq(VoL::Var(var)) => {
                    may_negate(format!("({} == {})", name, var), false ^ negated)
                }
                _ => {
                    todo!("Printing Var({}, {:?})", name, var_cond);
                }
            },
            _ => {
                todo!("{:?}", atom);
            }
        }
    }

    pub(super) fn display_guard(&self, guard: &Guard) -> String {
        if is_guard_dead(guard) {
            return "false".into();
        }
        match guard {
            Guard::N(negated, atom) => {
                if should_atom_replaced_with_cfg(atom) {
                    let cfg_atom_str = self.display_atom_as_cfg(atom, *negated);
                    let cfg_str = format!("cfg!({})", cfg_atom_str);
                    self.enclose_by_rust_tags(cfg_str, true)
                } else if should_atom_replaced_with_optional(atom) {
                    let optional_str = self.display_atom_as_optional(atom, *negated);
                    // Record if the variable is internal to the chunk (not an argument or return value)
                    let should_record = if let Atom::Var(name, _) = atom {
                        self.get_current_chunk_id()
                            .map(|chunk_id| self.analyzer.is_var_internal_for_chunk(chunk_id, name))
                            .unwrap_or(false)
                    } else {
                        false
                    };
                    self.enclose_by_rust_tags(optional_str, should_record)
                } else if self.full_rust_mode {
                    self.display_var_atom(atom, *negated)
                } else {
                    self.display_guard_as_test_command(guard)
                }
            }
            Guard::Or(guards) => {
                let guards_str = guards
                    .iter()
                    .map(|guard| self.display_guard(guard))
                    .join(" || ");
                guards_str
            }
            Guard::And(guards) => {
                let guards_str = guards
                    .iter()
                    .map(|guard| {
                        let guard_str = self.display_guard(guard);
                        if matches!(&guard, Guard::Or(_)) {
                            format!("({})", guard_str)
                        } else {
                            guard_str
                        }
                    })
                    .join(" && ");
                guards_str
            }
        }
    }

    fn display_guard_as_test_command(&self, guard: &Guard) -> String {
        match guard.print(&Default::default()) {
            Ok(s) => s,
            Err(required_node_ids) => guard
                .print(
                    &required_node_ids
                        .into_iter()
                        .map(|nid| (nid, self.display_node(nid, 0)))
                        .collect(),
                )
                .unwrap(),
        }
    }

    fn take_format_string_and_vars(&self, word: &AcWord) -> (String, Vec<String>) {
        self.in_format_string.replace(true);
        let word = self.display_word(word, false);
        let vars = self
            .formatted_vars
            .borrow_mut()
            .drain(..)
            .collect::<Vec<_>>();
        self.in_format_string.replace(false);
        let mut format_string = Self::escape_rust_string(&word);
        if vars.is_empty() {
            format_string = format_string.replace("}}", "}").replace("{{", "{");
        }
        self.count_num_consecutive_slashes(&format_string);
        (format_string, vars)
    }

    fn escape_rust_string(s: &str) -> String {
        s.chars()
            .map(|c| match c {
                '"' => "\\\"".to_string(),
                '\\' => "\\\\".to_string(),
                '\r' => "\\r".to_string(),
                '\t' => "\\t".to_string(),
                '\0' => "\\0".to_string(),
                c if c != '\n' && c.is_control() => format!("\\u{{{:04x}}}", c as u32),
                c => c.to_string(),
            })
            .collect()
    }

    fn count_num_consecutive_slashes(&self, s: &str) {
        let mut count = 0;
        for c in s.chars() {
            if c == '\\' {
                count += 1;
            } else {
                count = 0;
            }
        }
        if let Some(old) = self.max_num_consecutive_slashes.get() {
            count = old.max(count);
        }
        if count > 0 {
            self.max_num_consecutive_slashes.replace(Some(count));
        }
    }

    pub(super) fn display_ac_define(&self, key: &str, value: &str) -> String {
        let value = match value {
            "0" | "1" | "" => {
                // should be a boolean
                None
            }
            _ => Some(value),
        };
        let define_call = if let Some(policy) = self
            .analyzer
            .query_conditional_compilation_migration_policy(key)
        {
            match &policy.mig_type {
                CCMigrationType::Cfg => {
                    let key = policy.key.as_ref().unwrap();
                    self.func_requests.borrow_mut().found_define = true;
                    format!("define_cfg({:?}, {:?})", key, value)
                }
                CCMigrationType::Env => {
                    let key = policy.key.as_ref().unwrap();
                    self.func_requests.borrow_mut().found_define = true;
                    format!("define_env({:?}, {:?})", key, value.unwrap_or_default())
                }
                _ => return "".into(),
            }
        } else {
            self.func_requests.borrow_mut().found_define = true;
            format!("define_cfg({:?}, {:?})", key, value)
        };
        self.require_snippet(define_call.clone());
        define_call
    }

    fn display_ac_define_unquoted(&self, key: &AcWord, value: Option<&AcWord>) -> String {
        let (key_fstr, vars_in_key) = self.take_format_string_and_vars(key);
        let (value_fstr, vars_in_value) = match value {
            Some(word) => self.take_format_string_and_vars(word),
            None => (Default::default(), Default::default()),
        };
        let format_value = match value_fstr.as_str() {
            "0" | "1" | "" => {
                // should be a boolean
                assert!(vars_in_value.is_empty());
                None
            }
            "{}" => {
                let var = vars_in_value.first().unwrap();
                let expression = display_var_as_rust_str(var, &self.analyzer.get_data_type(var));
                Some(expression)
            }
            _ => Some(format!(
                "&format!(\"{}\", {})",
                value_fstr,
                vars_in_value
                    .iter()
                    .map(|var| format!("&{}", var))
                    .join(",")
            )),
        };
        if !vars_in_key.is_empty() {
            if !vars_in_value.is_empty() {
                todo!();
            }
            let format_key = format!(
                "&format!({:?}, {})",
                key_fstr,
                vars_in_key.iter().map(|var| "&".to_owned() + var).join(",")
            );
            let format_value = match format_value {
                Some(f) => format!("Some({f})"),
                None => "None".into(),
            };
            self.func_requests.borrow_mut().found_define = true;
            let define_call = format!("define_cfg({}, {})", format_key, format_value);
            self.require_snippet(define_call.clone());
            define_call
        } else {
            let define_call = if let Some(cpp_migration_policy) = self
                .analyzer
                .query_conditional_compilation_migration_policy(key_fstr.as_str())
            {
                match &cpp_migration_policy.mig_type {
                    CCMigrationType::Cfg => {
                        let format_value = match format_value {
                            Some(f) => format!("Some({f})"),
                            None => "None".into(),
                        };
                        self.func_requests.borrow_mut().found_define = true;
                        format!("define_cfg({:?}, {})", key_fstr, format_value)
                    }
                    CCMigrationType::Env => {
                        self.func_requests.borrow_mut().found_define = true;
                        format!(
                            "define_env({:?}, {})",
                            key_fstr,
                            format_value.unwrap_or("\"\"".into())
                        )
                    }
                    _ => return "".into(),
                }
            } else {
                let format_value = match format_value {
                    Some(f) => format!("Some({f})"),
                    None => "None".into(),
                };
                self.func_requests.borrow_mut().found_define = true;
                format!("define_cfg({:?}, {})", key_fstr, format_value)
            };
            self.require_snippet(define_call.clone());
            define_call
        }
    }

    fn display_ac_check_headers(
        &self,
        indent_level: usize,
        headers: &[String],
        action_if_found: Option<&Vec<NodeId>>,
        action_if_not_found: Option<&Vec<NodeId>>,
        includes: &str,
        defines: &HashMap<&str, String>,
    ) -> String {
        self.func_requests.borrow_mut().found_check_header = true;
        let tab = " ".repeat(indent_level * Self::TAB_WIDTH);
        let mut ret = String::new();
        for header in headers {
            let check_header = self.enclose_by_rust_tags(
                format!(
                    "check_header(cc, \"{}\", {:?}, &CPPFLAGS)",
                    header, includes
                ),
                false,
            );
            let define = defines
                .iter()
                .find_map(|(k, v)| k.contains(reproduce_cfg_name(header).as_str()).then_some(v))
                .map(|def| {
                    format!(
                        "\n{tab}{tab}{}",
                        self.enclose_by_rust_tags(def.to_owned(), true)
                    )
                })
                .unwrap_or_default();
            let action_if_found = action_if_found
                .map(|cmds| self.display_body(cmds, indent_level + 1))
                .unwrap_or_default();
            let action_if_not_found = action_if_not_found
                .map(|cmds| self.display_body(cmds, indent_level + 1))
                .unwrap_or_default();

            ret.push_str(&format!(
                "{tab}if {check_header} {{{define}\n{action_if_found}{tab}}}{}",
                if !action_if_not_found.is_empty() {
                    format!(" else {{\n{action_if_not_found}{tab}}}")
                } else {
                    "".into()
                },
            ));
        }
        ret
    }

    fn display_ac_check_libraries(
        &self,
        indent_level: usize,
        func: &str,
        libs: &[String],
        other_libs: &[String],
        action_if_found: Option<&Vec<NodeId>>,
        action_if_not_found: Option<&Vec<NodeId>>,
        try_std: bool,
        defines: &HashMap<&str, String>,
    ) -> String {
        self.func_requests.borrow_mut().found_check_library = true;
        let tab = " ".repeat(indent_level * Self::TAB_WIDTH);
        let tab_1 = " ".repeat((indent_level + 1) * Self::TAB_WIDTH);

        let mut ret = String::new();
        let func_call = format!(
            "check_library(cc, \"{}\", &{:?}, &{:?}, &LDFLAGS, {:?})",
            func, libs, other_libs, try_std
        );

        // For `check_library` call, recording is stopped
        // because we observed that the argument: `other_libs` can have a broken syntax. (e.g ["$var"])
        // self.require_snippet(func_call.clone());

        let check_library =
            self.enclose_by_rust_tags(format!("let Ok(opt) = {}", func_call), false);
        let append_libs = self.enclose_by_rust_tags("opt.map(|lib| LIBS.push(l))".into(), false);
        let action_if_found = action_if_found
            .map(|cmds| self.display_body(cmds, indent_level + 1))
            .unwrap_or_default();
        let action_if_not_found = action_if_not_found
            .map(|cmds| self.display_body(cmds, indent_level + 1))
            .unwrap_or_default();
        let defines = if defines.is_empty() {
            Default::default()
        } else {
            format!(
                "\n{tab_1}{}",
                defines
                    .values()
                    .map(|def| self.enclose_by_rust_tags(def.into(), true))
                    .join("\n")
            )
        };
        ret.push_str(&format!(
            "{tab}if {} {{\n{tab_1}{}{}\n{}{tab}}}{}",
            check_library,
            append_libs,
            defines,
            action_if_found,
            if action_if_not_found.is_empty() {
                Default::default()
            } else {
                format!(" else {{\n{action_if_not_found}{tab}}}")
            },
        ));
        ret
    }

    fn display_ac_check_decls(
        &self,
        indent_level: usize,
        symbols: &[String],
        action_if_found: Option<&Vec<NodeId>>,
        action_if_not_found: Option<&Vec<NodeId>>,
        includes: &str,
        defines: &HashMap<&str, String>,
    ) -> String {
        self.func_requests.borrow_mut().found_check_decl = true;
        let tab = " ".repeat(indent_level * Self::TAB_WIDTH);
        let mut ret = String::new();
        for symbol in symbols {
            let check_decl = self.enclose_by_rust_tags(
                format!("check_decl(cc, \"{}\", {:?}, &CPPFLAGS)", symbol, includes),
                false,
            );

            let define = defines
                .iter()
                .find_map(|(k, v)| k.contains(reproduce_cfg_name(symbol).as_str()).then_some(v))
                .map(|def| {
                    format!(
                        "\n{tab}{tab}{}",
                        self.enclose_by_rust_tags(def.to_owned(), true)
                    )
                })
                .unwrap_or_default();

            let action_if_found = action_if_found
                .map(|cmds| self.display_body(cmds, indent_level + 1))
                .unwrap_or_default();

            let action_if_not_found = action_if_not_found
                .map(|cmds| self.display_body(cmds, indent_level + 1))
                .unwrap_or_default();

            ret.push_str(&format!(
                "{tab}if {check_decl} {{{define}\n{action_if_found}{tab}}}{}",
                if action_if_not_found.is_empty() {
                    Default::default()
                } else {
                    format!(" else {{\n{action_if_not_found}{tab}}}")
                },
            ));
        }
        ret
    }

    fn display_ac_check_funcs(
        &self,
        indent_level: usize,
        functions: &[String],
        action_if_found: Option<&Vec<NodeId>>,
        action_if_not_found: Option<&Vec<NodeId>>,
        defines: &HashMap<&str, String>,
    ) -> String {
        self.func_requests.borrow_mut().found_check_func = true;
        let tab = " ".repeat(indent_level * Self::TAB_WIDTH);
        let mut ret = String::new();
        for function in functions {
            let check_func = self
                .enclose_by_rust_tags(format!("check_func(cc, \"{}\", &LDFLAGS)", function), false);

            let define = defines
                .iter()
                .find_map(|(k, v)| {
                    k.contains(reproduce_cfg_name(function).as_str())
                        .then_some(v)
                })
                .map(|def| {
                    format!(
                        "\n{tab}{tab}{}",
                        self.enclose_by_rust_tags(def.to_owned(), true)
                    )
                })
                .unwrap_or_default();

            let action_if_found = action_if_found
                .map(|cmds| self.display_body(cmds, indent_level + 1))
                .unwrap_or_default();

            let action_if_not_found = action_if_not_found
                .map(|cmds| self.display_body(cmds, indent_level + 1))
                .unwrap_or_default();

            ret.push_str(&format!(
                "{tab}if {check_func} {{{define}\n{action_if_found}{tab}}}{}",
                if !action_if_not_found.is_empty() {
                    format!(" else {{\n{action_if_not_found}{tab}}}")
                } else {
                    "".into()
                },
            ));
        }
        ret
    }

    /// Format a program string for use in check_compile/check_link calls.
    /// Handles shell variable substitution by generating format!() when needed.
    fn format_program_code(&self, prog: &str) -> String {
        // Regex to match $VAR or ${VAR} patterns
        let re = regex::Regex::new(r"\$\{?([A-Za-z_][A-Za-z0-9_]*)\}?").unwrap();

        let mut vars = Vec::new();
        let format_str = re.replace_all(prog, |caps: &regex::Captures| {
            let var_name = caps.get(1).unwrap().as_str();
            vars.push(var_name.to_string());
            "{}" // format! placeholder
        });

        if vars.is_empty() {
            // No shell variables: use simple string literal
            format!("{:?}", prog)
        } else {
            // Has shell variables: use format!() macro
            // Escape for Rust string, then escape braces except placeholders
            let escaped = Self::escape_rust_string(&format_str);
            // Escape { and } to {{ and }} except for our {} placeholders
            let mut result = String::new();
            let mut chars = escaped.chars().peekable();
            while let Some(c) = chars.next() {
                match c {
                    '{' => {
                        if chars.peek() == Some(&'}') {
                            // This is a {} placeholder, keep it
                            result.push('{');
                            result.push('}');
                            chars.next();
                        } else {
                            // Escape lone {
                            result.push_str("{{");
                        }
                    }
                    '}' => {
                        // Escape lone }
                        result.push_str("}}");
                    }
                    _ => result.push(c),
                }
            }
            format!("&format!(\"{}\", {})", result, vars.join(", "))
        }
    }

    fn display_ac_compile_check(
        &self,
        indent_level: usize,
        code: &str,
        action_if_true: Option<&Vec<NodeId>>,
        action_if_false: Option<&Vec<NodeId>>,
    ) -> String {
        self.func_requests.borrow_mut().found_check_compile = true;
        let tab = " ".repeat(indent_level * Self::TAB_WIDTH);

        let code_expr = self.format_program_code(code);
        let check_compile = self.enclose_by_rust_tags(
            format!("check_compile(&CC, &CFLAGS, &CPPFLAGS, {})", code_expr),
            false,
        );
        let action_if_true = action_if_true
            .map(|cmds| self.display_body(cmds, indent_level + 1))
            .unwrap_or_default();
        let action_if_false = action_if_false
            .map(|cmds| self.display_body(cmds, indent_level + 1))
            .unwrap_or_default();

        format!(
            "{tab}if {} {{\n{}{tab}}}{}",
            check_compile,
            action_if_true,
            if action_if_false.is_empty() {
                Default::default()
            } else {
                format!(" else {{\n{action_if_false}{tab}}}")
            },
        )
    }

    fn display_ac_link_check(
        &self,
        indent_level: usize,
        code: &str,
        action_if_true: Option<&Vec<NodeId>>,
        action_if_false: Option<&Vec<NodeId>>,
    ) -> String {
        self.func_requests.borrow_mut().found_check_link = true;
        let tab = " ".repeat(indent_level * Self::TAB_WIDTH);

        let code_expr = self.format_program_code(code);
        let check_link = self.enclose_by_rust_tags(
            format!("check_link(&CC, &CFLAGS, &LDFLAGS, &LIBS, {})", code_expr),
            false,
        );
        let action_if_true = action_if_true
            .map(|cmds| self.display_body(cmds, indent_level + 1))
            .unwrap_or_default();
        let action_if_false = action_if_false
            .map(|cmds| self.display_body(cmds, indent_level + 1))
            .unwrap_or_default();

        format!(
            "{tab}if {} {{\n{}{tab}}}{}",
            check_link,
            action_if_true,
            if action_if_false.is_empty() {
                Default::default()
            } else {
                format!(" else {{\n{action_if_false}{tab}}}")
            },
        )
    }

    fn display_pkg_check_modules(&self, node_id: NodeId, indent_level: usize) -> String {
        let tab = " ".repeat(indent_level * Self::TAB_WIDTH);
        let tab_1 = " ".repeat((indent_level + 1) * Self::TAB_WIDTH);

        let pkg_config = self.analyzer.pkg_config_analyzer();
        let info = pkg_config.get_pkg_check_modules_info(node_id).unwrap();

        let init_pkg_cflags = self.enclose_by_rust_tags(
            format!("let mut {} = Vec::new();", info.cflags_var_name),
            false,
        );
        let init_pkg_libs = self.enclose_by_rust_tags(
            format!("let mut {} = Vec::new();", info.libs_var_name),
            false,
        );
        let mut ret = format!("{tab}{}\n{tab}{}\n", init_pkg_cflags, init_pkg_libs);

        for (name, min_version) in &info.packages {
            if let Some(sys_info) = pkg_config.get_system_package_info(name) {
                self.func_requests.borrow_mut().found_pkg_config = true;
                let min_version_str = match min_version {
                    None => "None".into(),
                    Some(VoL::Var(var)) => format!("Some(&{})", var),
                    Some(VoL::Lit(lit)) => format!("Some(\"{}\")", lit),
                };
                let run_pkg_config = self.enclose_by_rust_tags(
                    format!(
                        "let Some((cflags, libs)) = run_pkg_config(\"{}\", {})",
                        name, min_version_str
                    ),
                    true,
                );

                let add_include_guard = self.enclose_by_rust_tags(
                    format!(
                        "{}.push(\"-D{}\".to_string());",
                        info.cflags_var_name, &sys_info.include_guard_macro_name
                    ),
                    false,
                );
                let add_pkg_cflags = self.enclose_by_rust_tags(
                    format!("{}.extend(cflags.iter().cloned());", info.cflags_var_name),
                    false,
                );
                let add_pkg_libs = self.enclose_by_rust_tags(
                    format!("{}.extend(libs.iter().cloned());", info.libs_var_name),
                    false,
                );

                let action_if_found = self.display_body(&info.action_if_found, indent_level + 1);
                let action_if_not_found =
                    self.display_body(&info.action_if_not_found, indent_level + 1);

                ret.push_str(&format!(
                    "{tab}if {} {{\n{tab_1}{}\n{tab_1}{}\n{tab_1}{}\n{}{tab}}}{}",
                    run_pkg_config,
                    add_include_guard,
                    add_pkg_cflags,
                    add_pkg_libs,
                    action_if_found,
                    if !action_if_not_found.is_empty() {
                        format!(" else {{\n{action_if_not_found}{tab}}}")
                    } else {
                        "".into()
                    },
                ));
            } else {
                let action_if_not_found =
                    self.display_body(&info.action_if_not_found, indent_level);
                if !action_if_not_found.is_empty() {
                    ret.push_str(&format!("{tab}{}", action_if_not_found));
                }
            }
        }
        ret
    }
}

pub(super) fn display_var_as_rust_str(var: &str, data_type: &DataType) -> String {
    match data_type {
        DataType::Boolean => format!("if {} {{ \"1\" }} else {{ \"0\" }}", var),
        DataType::Integer => format!("&{}.to_string()", var),
        DataType::List(_) => format!("&{}.join(\" \")", var),
        DataType::Path => format!("{}.to_str().unwrap()", var),
        DataType::Literal => format!("&{}", var),
        _ => unimplemented!(),
    }
}

impl<'a> NodePool<AcWord> for TranslatingPrinter<'a> {
    fn display_shell_word(&self, shell_word: &WordFragment<AcWord>) -> String {
        if self.in_format_string.get() {
            if let WordFragment::Param(Parameter::Var(var)) = shell_word {
                self.formatted_vars.borrow_mut().push(var.to_owned());
                return "{}".into();
            }
            if let WordFragment::Literal(lit) = shell_word {
                return lit.replace("{", "{{").replace("}", "}}");
            }
        }
        if self.in_literal_assignment.get() {
            if let WordFragment::Literal(lit) = shell_word {
                self.assigned_literals.borrow_mut().extend(
                    lit.split_whitespace()
                        .filter(|s| !s.is_empty())
                        .map(|s| s.to_owned()),
                );
                return lit.to_owned();
            }
        }

        match &shell_word {
            WordFragment::Escaped(lit) => match lit.as_str() {
                "`" => lit.into(),
                _ => format!("\\{}", lit),
            },
            _ => self.shell_word_to_string(shell_word),
        }
    }

    fn display_parameter_substitution(
        &self,
        param_subst: &ParameterSubstitution<AcWord>,
    ) -> String {
        // we want to collect literals in assignment, but not ones in parameter substitution.
        let saved = self.in_literal_assignment.replace(false);
        let ret = self.parameter_substitution_to_string(param_subst);
        self.in_literal_assignment.replace(saved);
        ret
    }

    fn display_inner_param(&self, param: &Parameter<String>) -> String {
        if matches!(param, Parameter::Var(_)) {
            let loc = self.take_location();
            if let Some((dict_name, access, value_type)) = self.dict_accesses.get(&loc) {
                return self.display_dictionary_read(dict_name, access, value_type);
            }
        }
        self.inner_param_to_string(param)
    }

    fn display_assignment(&self, name: &str, word: &AcWord, indent_level: usize) -> String {
        let tab = " ".repeat(indent_level * Self::TAB_WIDTH);
        self.in_literal_assignment.set(true);
        let rhs = self.display_word(word, false);
        self.in_literal_assignment.set(false);
        let assigned_literals = self
            .assigned_literals
            .borrow_mut()
            .drain(..)
            .dedup()
            .collect::<Vec<_>>();
        if assigned_literals.len() > 10 {
            // these must be the literals that initialize a large list.
            // we want to force LLMs emit them exactly.
            for lit in assigned_literals {
                self.require_snippet(lit);
            }
        }
        let loc = self.take_location();
        if let Some((dict_name, access, value_type)) = self.dict_accesses.get(&loc) {
            format!(
                "{tab}{}",
                self.display_dictionary_write(dict_name, access, value_type, Some(&rhs))
            )
        } else {
            format!("{tab}{}=\"{}\"", name, rhs)
        }
    }

    fn display_arithmetic(&self, arith: &Arithmetic<String>) -> String {
        use Arithmetic::*;
        if matches!(
            arith,
            Var(_) | PostIncr(_) | PostDecr(_) | PreIncr(_) | PreDecr(_)
        ) {
            let loc = self.take_location();
            if let Some((dict_name, access, value_type)) = self.dict_accesses.get(&loc) {
                return self.display_dictionary_read(dict_name, access, value_type);
            }
        }
        arith.to_string()
    }

    fn display_case(
        &self,
        word: &AcWord,
        arms: &[PatternBodyPair<AcWord>],
        indent_level: usize,
    ) -> String {
        if arms.is_empty() {
            return String::new();
        }
        let tab = " ".repeat(indent_level * Self::TAB_WIDTH);
        let target = self.display_word(word, false);
        let node_id = self.node_cursor.get().unwrap();
        let block_ids = &self.analyzer.get_node(node_id).unwrap().info.branches;
        let guards = block_ids
            .iter()
            .map(|block_id| self.analyzer.get_block(*block_id).guards.last().unwrap())
            .collect::<Vec<_>>();
        assert_eq!(arms.len(), guards.len());
        let should_replace_with_ifelse = guards
            .iter()
            .all(|guard| should_guard_replaced(guard) || is_guard_dead(guard));
        if should_replace_with_ifelse {
            assert_eq!(arms.len(), guards.len());
            let mut iter = arms.iter().zip(guards.iter());
            let first_if = {
                let (arm, guard) = iter.next().unwrap();
                format!(
                    "{tab}if {}; then\n{}",
                    self.display_guard(guard),
                    self.display_body(&arm.body, indent_level + 1)
                )
            };
            let mut else_if = String::new();
            let mut else_branch = None;
            for (arm, guard) in iter {
                if is_guard_dead(guard) {
                    continue;
                }
                if matches!(guard, Guard::N(false, Atom::Arg(_, VarCond::MatchAny))) {
                    else_branch.replace(format!(
                        "{tab}else\n{}",
                        self.display_body(&arm.body, indent_level + 1)
                    ));
                } else {
                    else_if.push_str(&format!(
                        "{tab}else if {}; then\n{}",
                        self.display_guard(guard),
                        self.display_body(&arm.body, indent_level + 1)
                    ));
                }
            }
            let rest = match else_branch {
                Some(s) => format!("{}{tab}fi", s),
                None => format!("{tab}fi"),
            };
            format!("{}{}{}", first_if, else_if, rest)
        } else {
            let mut arms = arms
                .iter()
                .zip(guards.iter())
                .map(|(arm, guard)| {
                    let pattern = if should_guard_replaced(guard) {
                        self.display_guard(guard)
                    } else {
                        arm.patterns
                            .iter()
                            .map(|w| self.display_word(w, false))
                            .collect::<Vec<String>>()
                            .join("|")
                    };
                    format!(
                        "{tab}  {})\n{}{tab}    ;;",
                        pattern,
                        self.display_body(&arm.body, indent_level + 2)
                    )
                })
                .collect::<Vec<String>>()
                .join("\n");
            if !arms.is_empty() {
                arms.push('\n');
            }
            format!("{tab}case {} in\n{}{tab}esac", target, arms)
        }
    }

    fn display_condition(&self, cond: &Condition<AcWord>) -> String {
        if let Some(branch_index) = self.branch_cursor.get() {
            let node_id = self.node_cursor.get().unwrap();
            let block_id = &self.analyzer.get_node(node_id).unwrap().info.branches[branch_index];
            match self.analyzer.get_block(*block_id).guards.last() {
                Some(guard) if should_guard_replaced(guard) => {
                    return self.display_guard(guard);
                }
                Some(Guard::N(negated, Atom::Tautology)) => {
                    if *negated {
                        return "false".into();
                    } else {
                        return "true".into();
                    }
                }
                _ => (),
            }
        }
        self.condition_to_string(cond)
    }

    fn display_if(
        &self,
        conditionals: &[GuardBodyPair<AcWord>],
        else_branch: &[NodeId],
        indent_level: usize,
    ) -> String {
        let tab = " ".repeat(indent_level * Self::TAB_WIDTH);

        let first_if = {
            let pair = conditionals.first().unwrap();
            self.branch_cursor.set(Some(0));
            format!(
                "{tab}if {}; then\n{}",
                self.display_condition(&pair.condition),
                self.display_body(&pair.body, indent_level + 1)
            )
        };
        let else_if = conditionals
            .iter()
            .enumerate()
            .skip(1)
            .map(|(i, pair)| {
                self.branch_cursor.set(Some(i));
                format!(
                    "{tab}else if {}; then\n{}",
                    self.display_condition(&pair.condition),
                    self.display_body(&pair.body, indent_level + 1)
                )
            })
            .collect::<String>();
        let rest = if else_branch.is_empty() {
            format!("{tab}fi")
        } else {
            self.branch_cursor.set(Some(conditionals.len()));
            format!(
                "{tab}else\n{}{tab}fi",
                self.display_body(else_branch, indent_level + 1)
            )
        };
        self.branch_cursor.set(None);
        format!("{}{}{}", first_if, else_if, rest)
    }

    fn display_for(
        &self,
        var: &str,
        words: &[AcWord],
        body: &[NodeId],
        indent_level: usize,
    ) -> String {
        let tab = " ".repeat(indent_level * Self::TAB_WIDTH);
        let list = words
            .iter()
            .map(|w| self.display_word(w, true))
            .collect::<Vec<String>>()
            .join(" ");
        self.take_location(); // var
        format!(
            "{tab}for {var} in {list}; do\n{}{tab}done",
            self.display_body(body, indent_level + 1)
        )
    }

    fn display_cmd(&self, words: &[AcWord], indent_level: usize) -> String {
        let tab = " ".repeat(indent_level * Self::TAB_WIDTH);
        if let Some(first) = words.first() {
            if is_eval(first) {
                // FIXME: for the simplicity, we have two assumptions here.
                // 1. in eval assignments, only one dictionary gets touched, either written or read.
                // 2. the side where the dictionary appears, we won't see any other expressions
                //    such as literals.
                let node_id = self.node_cursor.get().unwrap();
                if let Some((_, (dict_name, access, value_type))) = self
                    .dict_accesses
                    .iter()
                    .find(|(loc, _)| loc.node_id == node_id)
                {
                    match access.operation {
                        DictionaryOperation::Write => {
                            return self
                                .display_dictionary_write(dict_name, access, value_type, None);
                        }
                        DictionaryOperation::Read => {
                            let lhs = access.assigned_to.clone().unwrap();
                            let rhs = self.enclose_by_rust_tags(
                                self.display_dictionary_read(dict_name, access, value_type),
                                false,
                            );
                            return format!("{tab}{}={}", lhs, rhs);
                        }
                    }
                }
            }
            if as_single(first)
                .and_then(as_shell)
                .and_then(as_literal)
                .is_some_and(|cmd| cmd == "sed")
            {
                self.func_requests.borrow_mut().found_sed = true;
            }
        }
        self.cmd_to_string(words, indent_level)
    }

    fn display_redirect_cmd(
        &self,
        cmd: NodeId,
        redirects: &[Redirect<AcWord>],
        indent_level: usize,
    ) -> String {
        if !redirects.is_empty() {
            self.func_requests.borrow_mut().found_redirection = true;
        }
        let tab = " ".repeat(indent_level * Self::TAB_WIDTH);
        if redirects.len() == 2 {
            if let (Redirect::Write(_, file), Redirect::Heredoc(_, heredoc)) =
                (&redirects[0], &redirects[1])
            {
                if let Word::Single(MayM4::Shell(WordFragment::Literal(filename))) = &file.0 {
                    let rust_string = {
                        let path = format!("Path::new(\"{}\")", filename);
                        self.require_snippet(path.clone());

                        // Use heredoc placeholder system for LLM-friendly output
                        let (format_string, vars) = self.take_format_string_and_vars(heredoc);
                        let placeholder =
                            self.create_heredoc_placeholder(format_string, vars.len());
                        self.require_snippet(placeholder.clone());

                        // Build the content string using the placeholder
                        let content = if vars.is_empty() {
                            format!("\"{}\"", placeholder)
                        } else {
                            format!("&format!(\"{}\", {})", placeholder, vars.join(", "))
                        };

                        self.enclose_by_rust_tags(
                            format!("write_file({}, {})", path, content),
                            false,
                        )
                    };
                    return format!("{tab}{}", rust_string);
                }
            }
        }
        self.redirect_cmd_to_string(cmd, redirects, indent_level)
    }
}

impl<'a> TranslatingPrinter<'a> {
    fn display_macro_arg_program(&self, macro_call: &M4Macro, index: usize) -> Option<String> {
        macro_call
            .get_arg_as_program(index)
            .map(|prog| self.display_word(&prog, false))
    }
}

impl<'a> DisplayM4 for TranslatingPrinter<'a> {
    fn display_m4_macro(&self, macro_call: &M4Macro, indent_level: usize) -> String {
        let tab = " ".repeat(indent_level * Self::M4_TAB_WIDTH);
        let node_id = self.node_cursor.get().unwrap();
        if let Some(effects) = self.analyzer.side_effects_of_frozen_macros().get(&node_id) {
            return effects
                .vars
                .iter()
                .map(|(name, (attrs, value))| match attrs.usage {
                    VarUsage::Defined => format!("{tab}{}=\"{}\"", name, value),
                    VarUsage::Append => format!("{tab}{}=\"{} {}\"", name, name, value),
                    VarUsage::Referenced => unreachable!(),
                })
                .join("\n");
        }
        // Track required define calls for hint comment
        let mut required_defines: HashMap<&str, String> = HashMap::new();

        if let Some(effects) = &macro_call.effects {
            if let Some(shell_vars) = &effects.shell_vars {
                for var in shell_vars {
                    if var.is_used() {
                        self.take_location();
                    }
                    if var.is_defined() {
                        self.take_location();
                    }
                }
            }
            // Process CPP symbols from macro effects
            if let Some(cpp_symbols) = &effects.cpp_symbols {
                for cpp in cpp_symbols {
                    if let Some(policy) = self
                        .analyzer
                        .query_conditional_compilation_migration_policy(&cpp.name)
                    {
                        match &policy.mig_type {
                            CCMigrationType::Cfg => {
                                let key = policy.key.as_ref().unwrap();
                                self.require_snippet(key.into());
                                self.func_requests.borrow_mut().found_define = true;
                                // not sure about the value, so let's leave the function call unfinished.
                                // despite this kind of broken syntax, LLMs will complete it (wow).
                                required_defines.insert(key, format!("define_cfg({:?},", key));
                            }
                            CCMigrationType::Env => {
                                let key = policy.key.as_ref().unwrap();
                                self.require_snippet(key.into());
                                self.func_requests.borrow_mut().found_define = true;
                                // not sure about the value, so let's leave the function call unfinished.
                                required_defines.insert(key, format!("define_env({:?},", key,));
                            }
                            _ => (),
                        }
                    }
                }
            }
        }

        match macro_call.name.as_str() {
            "AC_INIT" => {
                let comment = format!(
                    "{tab}# Sample translation of AC_INIT (You can reduce local variables)\n"
                );
                let body = get_function_body_ac_init();
                if !required_defines.is_empty() {
                    for req_def in required_defines.values() {
                        self.require_snippet(req_def.clone());
                    }
                    let hint = format!(
                        "{tab}# NOTE: You MUST include: {} appropriately.\n",
                        required_defines.values().join(", ")
                    );
                    format!("{comment}{hint}{body}")
                } else {
                    format!("{comment}{body}")
                }
            }
            "AM_INIT_AUTOMAKE" => {
                let comment = format!("{tab}# Sample translation of AM_INIT_AUTOMAKE (You can reduce local variables)\n");
                let body = get_function_body_am_init_automake();
                if !required_defines.is_empty() {
                    for req_def in required_defines.values() {
                        self.require_snippet(req_def.clone());
                    }
                    let hint = format!(
                        "{tab}# NOTE: You MUST include: {} appropriately.\n",
                        required_defines.values().join(", ")
                    );
                    format!("{comment}{hint}{body}")
                } else {
                    format!("{comment}{body}")
                }
            }
            "AC_CACHE_CHECK" => {
                let description = macro_call.get_arg_as_literal(0).unwrap();
                let body = macro_call.get_arg_as_cmd(2).unwrap();
                format!(
                    "{tab}# Check {description}\n{}",
                    self.display_body(&body, indent_level)
                )
            }
            "AC_CONFIG_LINKS" => {
                // FIXME: the second and third args are rarely used but we ignored them anyway
                let links: Vec<(String, String)> = if let Some(tags) = macro_call
                    .effects
                    .as_ref()
                    .and_then(|eff| eff.tags.as_ref())
                {
                    tags.iter()
                        .filter_map(|(dst, src_opt)| {
                            src_opt.as_ref().map(|src| (dst.to_owned(), src.to_owned()))
                        })
                        .collect()
                } else {
                    let tags = macro_call.get_arg_as_array(0).unwrap();
                    tags.iter()
                        .flat_map(split_tag_word)
                        .map(|(dst, src)| {
                            (self.display_word(&dst, true), self.display_word(&src, true))
                        })
                        .collect()
                };
                links
                    .into_iter()
                    .map(|(dst, src)| format!("{tab}ln -s {src} {dst}"))
                    .join("\n")
            }
            "AC_DEFINE" => {
                let key = match macro_call.args.first().unwrap() {
                    M4Argument::Word(word) => self.display_word(word, false),
                    M4Argument::Literal(lit) => lit.to_owned(),
                    _ => unreachable!(),
                };
                let value = macro_call.get_arg_as_literal(1).unwrap_or_default();
                let ret = self.display_ac_define(&key, &value);
                format!("{tab}{}", self.enclose_by_rust_tags(ret, false))
            }
            "AC_DEFINE_UNQUOTED" => {
                let key = match macro_call.args.first().unwrap() {
                    M4Argument::Word(word) => word,
                    M4Argument::Literal(lit) => &(lit.clone().into()),
                    _ => unreachable!(),
                };
                let value = match macro_call.args.get(1) {
                    Some(M4Argument::Word(word)) => Some(word),
                    Some(M4Argument::Literal(lit)) => Some(&(lit.clone().into())),
                    None => None,
                    _ => unreachable!(),
                };
                let ret = self.display_ac_define_unquoted(key, value);
                format!("{tab}{}", self.enclose_by_rust_tags(ret, false))
            }
            "AC_CHECK_HEADER" => {
                let header = match macro_call.args.first().unwrap() {
                    M4Argument::Word(word) => self.display_word(word, false),
                    M4Argument::Literal(lit) => lit.clone(),
                    _ => unreachable!(),
                };
                let action_if_found = macro_call.get_arg_as_cmd(1);
                let action_if_not_found = macro_call.get_arg_as_cmd(2);
                let includes = self
                    .display_macro_arg_program(macro_call, 3)
                    .unwrap_or_default();
                self.display_ac_check_headers(
                    indent_level,
                    &[header],
                    action_if_found.as_ref(),
                    action_if_not_found.as_ref(),
                    &includes,
                    &required_defines,
                )
            }
            "AC_CHECK_HEADERS" => {
                let headers = macro_call
                    .get_arg_as_array(0)
                    .unwrap_or_default()
                    .into_iter()
                    .map(|word| self.display_word(&word, false))
                    .collect::<Vec<_>>();
                let action_if_found = macro_call.get_arg_as_cmd(1);
                let action_if_not_found = macro_call.get_arg_as_cmd(2);
                let includes = self
                    .display_macro_arg_program(macro_call, 3)
                    .unwrap_or_default();
                self.display_ac_check_headers(
                    indent_level,
                    &headers,
                    action_if_found.as_ref(),
                    action_if_not_found.as_ref(),
                    &includes,
                    &required_defines,
                )
            }
            "AC_CHECK_LIB" => {
                let library = match macro_call.args.first().unwrap() {
                    M4Argument::Word(word) => self.display_word(word, false),
                    M4Argument::Literal(lit) => lit.clone(),
                    _ => unreachable!(),
                };
                let function = match macro_call.args.get(1).unwrap() {
                    M4Argument::Word(word) => self.display_word(word, false),
                    M4Argument::Literal(lit) => lit.clone(),
                    _ => unreachable!(),
                };
                let action_if_found = macro_call.get_arg_as_cmd(2);
                let action_if_not_found = macro_call.get_arg_as_cmd(3);
                let other_libs = macro_call
                    .get_arg_as_array(4)
                    .unwrap_or_default()
                    .into_iter()
                    .map(|word| self.display_word(&word, false))
                    .collect::<Vec<_>>();
                self.display_ac_check_libraries(
                    indent_level,
                    &function,
                    &[library],
                    &other_libs,
                    action_if_found.as_ref(),
                    action_if_not_found.as_ref(),
                    false,
                    &required_defines,
                )
            }
            "AC_SEARCH_LIBS" => {
                let function = match macro_call.args.first().unwrap() {
                    M4Argument::Word(word) => self.display_word(word, false),
                    M4Argument::Literal(lit) => lit.clone(),
                    _ => unreachable!(),
                };
                let libraries = macro_call
                    .get_arg_as_array(1)
                    .unwrap_or_default()
                    .into_iter()
                    .map(|word| self.display_word(&word, false))
                    .collect::<Vec<_>>();
                let action_if_found = macro_call.get_arg_as_cmd(2);
                let action_if_not_found = macro_call.get_arg_as_cmd(3);
                let other_libs = macro_call
                    .get_arg_as_array(4)
                    .unwrap_or_default()
                    .into_iter()
                    .map(|word| self.display_word(&word, false))
                    .collect::<Vec<_>>();
                self.display_ac_check_libraries(
                    indent_level,
                    &function,
                    &libraries,
                    &other_libs,
                    action_if_found.as_ref(),
                    action_if_not_found.as_ref(),
                    true,
                    &required_defines,
                )
            }
            "AC_CHECK_DECL" => {
                let symbol = match macro_call.args.first().unwrap() {
                    M4Argument::Word(word) => self.display_word(word, false),
                    M4Argument::Literal(lit) => lit.clone(),
                    _ => unreachable!(),
                };
                let action_if_found = macro_call.get_arg_as_cmd(1);
                let action_if_not_found = macro_call.get_arg_as_cmd(2);
                let includes = self
                    .display_macro_arg_program(macro_call, 3)
                    .unwrap_or_default();
                self.display_ac_check_decls(
                    indent_level,
                    &[symbol],
                    action_if_found.as_ref(),
                    action_if_not_found.as_ref(),
                    &includes,
                    &required_defines,
                )
            }
            "AC_CHECK_DECLS" => {
                let symbols = macro_call
                    .get_arg_as_array(0)
                    .unwrap_or_default()
                    .into_iter()
                    .map(|word| self.display_word(&word, false))
                    .collect::<Vec<_>>();
                let action_if_found = macro_call.get_arg_as_cmd(1);
                let action_if_not_found = macro_call.get_arg_as_cmd(2);
                let includes = self
                    .display_macro_arg_program(macro_call, 3)
                    .unwrap_or_default();
                self.display_ac_check_decls(
                    indent_level,
                    &symbols,
                    action_if_found.as_ref(),
                    action_if_not_found.as_ref(),
                    &includes,
                    &required_defines,
                )
            }
            "AC_CHECK_FUNC" => {
                let function = match macro_call.args.first().unwrap() {
                    M4Argument::Word(word) => self.display_word(word, false),
                    M4Argument::Literal(lit) => lit.clone(),
                    _ => unreachable!(),
                };
                let action_if_found = macro_call.get_arg_as_cmd(1);
                let action_if_not_found = macro_call.get_arg_as_cmd(2);
                self.display_ac_check_funcs(
                    indent_level,
                    &[function],
                    action_if_found.as_ref(),
                    action_if_not_found.as_ref(),
                    &required_defines,
                )
            }
            "AC_CHECK_FUNCS" => {
                let functions = macro_call
                    .get_arg_as_array(0)
                    .unwrap_or_default()
                    .into_iter()
                    .map(|word| self.display_word(&word, false))
                    .collect::<Vec<_>>();
                let action_if_found = macro_call.get_arg_as_cmd(1);
                let action_if_not_found = macro_call.get_arg_as_cmd(2);
                self.display_ac_check_funcs(
                    indent_level,
                    &functions,
                    action_if_found.as_ref(),
                    action_if_not_found.as_ref(),
                    &required_defines,
                )
            }
            "PKG_CHECK_MODULES" => self.display_pkg_check_modules(node_id, indent_level),
            "AC_COMPILE_IFELSE" => {
                // AC_COMPILE_IFELSE([input], [action-if-true], [action-if-false])
                let code = self
                    .display_macro_arg_program(macro_call, 0)
                    .unwrap_or_default();
                let action_if_true = macro_call.get_arg_as_cmd(1);
                let action_if_false = macro_call.get_arg_as_cmd(2);
                self.display_ac_compile_check(
                    indent_level,
                    &code,
                    action_if_true.as_ref(),
                    action_if_false.as_ref(),
                )
            }
            "AC_TRY_COMPILE" => {
                // AC_TRY_COMPILE([includes], [function-body], [action-if-true], [action-if-false])
                let includes = self
                    .display_macro_arg_program(macro_call, 0)
                    .unwrap_or_default();
                let body = self
                    .display_macro_arg_program(macro_call, 1)
                    .unwrap_or_default();
                let code = format!("{}\nint main() {{ {} return 0; }}", includes, body);
                let action_if_true = macro_call.get_arg_as_cmd(2);
                let action_if_false = macro_call.get_arg_as_cmd(3);
                self.display_ac_compile_check(
                    indent_level,
                    &code,
                    action_if_true.as_ref(),
                    action_if_false.as_ref(),
                )
            }
            "AC_LINK_IFELSE" => {
                // AC_LINK_IFELSE([input], [action-if-true], [action-if-false])
                let code = self
                    .display_macro_arg_program(macro_call, 0)
                    .unwrap_or_default();
                let action_if_true = macro_call.get_arg_as_cmd(1);
                let action_if_false = macro_call.get_arg_as_cmd(2);
                self.display_ac_link_check(
                    indent_level,
                    &code,
                    action_if_true.as_ref(),
                    action_if_false.as_ref(),
                )
            }
            "AC_TRY_LINK" => {
                // AC_TRY_LINK([includes], [function-body], [action-if-true], [action-if-false])
                let includes = self
                    .display_macro_arg_program(macro_call, 0)
                    .unwrap_or_default();
                let body = self
                    .display_macro_arg_program(macro_call, 1)
                    .unwrap_or_default();
                let code = format!("{}\nint main() {{ {} return 0; }}", includes, body);
                let action_if_true = macro_call.get_arg_as_cmd(2);
                let action_if_false = macro_call.get_arg_as_cmd(3);
                self.display_ac_link_check(
                    indent_level,
                    &code,
                    action_if_true.as_ref(),
                    action_if_false.as_ref(),
                )
            }
            _ => {
                self.called_macros
                    .borrow_mut()
                    .push(macro_call.name.clone());
                // Add hint comment for LLM guidance when CPP symbols need define_cfg/define_env
                let macro_output = self.m4_macro_to_string(macro_call, indent_level);
                if !required_defines.is_empty() {
                    for req_def in required_defines.values() {
                        self.require_snippet(req_def.clone());
                    }
                    let hint = format!(
                        "{tab}# NOTE: You MUST include: {} appropriately.\n",
                        required_defines.values().join(", ")
                    );
                    format!("{}{}", hint, macro_output)
                } else {
                    macro_output
                }
            }
        }
    }

    fn display_may_m4_word(&self, frag: &AcWordFragment) -> String {
        if let MayM4::Macro(macro_word) = frag {
            match macro_word.name.as_str() {
                "AC_LANG_SOURCE" => {
                    let body = self
                        .display_macro_arg_program(macro_word, 0)
                        .unwrap_or_default();
                    // FIXME: actually we have to consider dynamically defined cpp symbols here
                    return body;
                }
                "AC_LANG_PROGRAM" => {
                    let prologue = self
                        .display_macro_arg_program(macro_word, 0)
                        .unwrap_or_default();
                    let body = self
                        .display_macro_arg_program(macro_word, 1)
                        .unwrap_or_default();
                    let code = format!("{}\nint main() {{ {} return 0; }}", prologue, body);
                    return code;
                }
                "AC_INCLUDES_DEFAULT" => {
                    // TODO: put placeholder instead
                    return pretranslation::get_expansion_ac_includes_default().into();
                }
                _ => {
                    // fall thru
                }
            }
        }
        self.may_m4_word_to_string(frag)
    }
}

fn should_guard_replaced(guard: &Guard) -> bool {
    match guard {
        Guard::N(_, atom) => {
            should_atom_replaced_with_cfg(atom) || should_atom_replaced_with_optional(atom)
        }
        Guard::Or(guards) | Guard::And(guards) => guards.iter().any(should_guard_replaced),
    }
}

fn is_guard_dead(guard: &Guard) -> bool {
    match guard {
        Guard::N(true, Atom::Tautology) => true,
        Guard::N(_, _) => false,
        Guard::Or(guards) => guards.iter().any(is_guard_dead),
        Guard::And(guards) => guards.iter().all(is_guard_dead),
    }
}

fn should_atom_replaced_with_cfg(atom: &Atom) -> bool {
    use Atom::*;
    match atom {
        Arch(_) | Cpu(_) | Os(_) | Env(_) | Abi(_) | Arg(_, _) => true,
        _ => false,
    }
}

fn should_atom_replaced_with_optional(atom: &Atom) -> bool {
    use Atom::*;
    match atom {
        Var(_, VarCond::Set | VarCond::Unset) => true,
        _ => false,
    }
}

fn split_tag_word(tag: &AcWord) -> Option<(AcWord, AcWord)> {
    if let Word::Concat(words) = &tag.0 {
        if let Some(colon_pos) = words.iter().position(|w| {
            as_shell(w)
                .map(|frag| frag == &WordFragment::Colon)
                .unwrap_or_default()
        }) {
            let first = Word::Concat(words[..colon_pos].to_vec()).into();
            let after_words = words[colon_pos + 1..].to_vec();
            let second = if after_words.is_empty() {
                Word::Empty
            } else {
                Word::Concat(after_words)
            }
            .into();
            return Some((first, second));
        }
    }
    None
}

fn reproduce_cfg_name(s: &str) -> String {
    sanitize_c_name(s).to_lowercase()
}

// the same function as the macro database
fn sanitize_c_name(s: &str) -> String {
    s.chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() {
                c.to_uppercase().next().unwrap()
            } else if c == '*' {
                'P'
            } else {
                '_'
            }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_escape_rust_string() {
        // Test basic strings
        assert_eq!(TranslatingPrinter::escape_rust_string("hello"), "hello");

        // Test control characters that need escaping
        assert_eq!(
            TranslatingPrinter::escape_rust_string(r#"{ '\001', '\002', '\003' }"#),
            r#"{ '\\001', '\\002', '\\003' }"#
        );

        // Test quote and escaped characters that need escaping
        assert_eq!(
            TranslatingPrinter::escape_rust_string(r#"printf ("%d %f\n", foo, bar);"#),
            r#"printf (\"%d %f\\n\", foo, bar);"#
        );

        // Test special characters that need escaping
        assert_eq!(
            TranslatingPrinter::escape_rust_string("hello\tworld"),
            "hello\\tworld"
        );
        assert_eq!(
            TranslatingPrinter::escape_rust_string("hello\rworld"),
            "hello\\rworld"
        );
        assert_eq!(
            TranslatingPrinter::escape_rust_string("hello\"world"),
            "hello\\\"world"
        );
        assert_eq!(
            TranslatingPrinter::escape_rust_string("hello\\world"),
            "hello\\\\world"
        );
        assert_eq!(
            TranslatingPrinter::escape_rust_string("hello\0world"),
            "hello\\0world"
        );
    }
}
