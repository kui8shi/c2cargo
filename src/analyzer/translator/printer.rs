use std::{
    cell::{Cell, RefCell},
    collections::HashMap,
};

use super::InlinedTranslationOutput;
use crate::analyzer::{
    as_literal, as_shell,
    build_option::FeatureState,
    chunk::ChunkId,
    conditional_compilation::CCMigrationType,
    dictionary::{DictionaryAccess, DictionaryOperation, DictionaryValue},
    guard::{Atom, VarCond, VoL},
    location::Location,
    translator::pretranslation::get_function_body_ac_init,
    type_inference::DataType,
    variable::is_eval,
    Analyzer, BlockId, Guard, NodeInfo,
};
use autotools_parser::{
    ast::{
        minimal::Word,
        node::{
            AcCommand, AcWord, Condition, DisplayM4, DisplayNode, GuardBodyPair, M4Macro, Node,
            NodeId, NodePool, PatternBodyPair, WordFragment,
        },
        Arithmetic, MayM4, Parameter, Redirect,
    },
    m4_macro::{M4Argument, VarUsage},
};

use itertools::Itertools;

pub(crate) struct TranslatingPrinter<'a> {
    /// Contains all stateful information
    analyzer: &'a Analyzer,
    /// Assigned the id of top-most node while formatting a tree of nodes.
    top_most: Cell<Option<NodeId>>,
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
    translated_fragments: RefCell<Vec<String>>,
    /// Whether parameters are to be displayed in the style of rust's format string
    in_format_string: Cell<bool>,
    /// When `in_format_string` is set to true, we record appeared variables here.
    formatted_vars: RefCell<Vec<String>>,
    /// Appeared chunks when embedding
    embedded_chunks: RefCell<HashMap<ChunkId, String>>,
    /// Appeared features
    cargo_features: RefCell<Vec<String>>,
    /// Simple translations available for inlining
    inlined_translations: &'a HashMap<ChunkId, InlinedTranslationOutput>,
    /// Whether we have found a usage of redirection.
    found_redirection: Cell<bool>,
    /// Whether we have found a usage of sed command.
    found_sed: Cell<bool>,
    /// Whether we have found a usage of define_cfg/define_env
    found_define: Cell<bool>,
    /// Whether we have found a usage of pkg_config
    found_pkg_config: Cell<bool>,
    /// Whether we have found a usage of AC_CHECK_HEADER/AC_CHECK_HEADERS
    found_check_header: Cell<bool>,
    /// Whether we have found a usage of AC_CHECK_LIB/AC_SEARCH_LIBS
    found_check_library: Cell<bool>,
    /// Whether we have found a usage of AC_CHECK_DECL/AC_CHECK_DECLS
    found_check_decl: Cell<bool>,
}

impl<'a> std::fmt::Debug for TranslatingPrinter<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Printer")
            .field("forcus", &self.top_most)
            .finish()
    }
}

impl<'a> TranslatingPrinter<'a> {
    /// Construct a new printer with inlined translations for inlining
    pub fn new(
        analyzer: &'a Analyzer,
        inlined_translations: &'a HashMap<ChunkId, InlinedTranslationOutput>,
        full_rust_mode: bool,
    ) -> Self {
        let mut dict_accesses = HashMap::new();
        for dict in analyzer.dicts.as_ref().unwrap() {
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
            top_most: Cell::new(None),
            node_cursor: Cell::new(None),
            branch_cursor: Cell::new(None),
            order: Cell::new(0),
            full_rust_mode,
            dict_accesses,
            translated_fragments: RefCell::new(Vec::new()),
            in_format_string: Cell::new(false),
            formatted_vars: RefCell::new(Vec::new()),
            embedded_chunks: RefCell::new(HashMap::new()),
            cargo_features: RefCell::new(Vec::new()),
            inlined_translations,
            found_redirection: Cell::new(false),
            found_sed: Cell::new(false),
            found_define: Cell::new(false),
            found_pkg_config: Cell::new(false),
            found_check_header: Cell::new(false),
            found_check_library: Cell::new(false),
            found_check_decl: Cell::new(false),
        }
    }

    pub fn get_node(&self, node_id: NodeId) -> Option<&Node<AcCommand, NodeInfo>> {
        self.analyzer.get_node(node_id)
    }

    pub fn print_node(&self, node_id: NodeId) -> String {
        self.display_node(node_id, 0)
    }

    pub fn record_translated_fragment(&self, frag: String) {
        self.translated_fragments.borrow_mut().push(frag);
    }

    pub fn get_translated_fragments(&self) -> Vec<String> {
        self.translated_fragments.borrow().clone()
    }

    pub fn get_cargo_features(&self) -> Vec<String> {
        self.cargo_features.borrow().clone()
    }

    fn enclose_by_rust_tags(&self, fragment: String, record: bool) -> String {
        if self.full_rust_mode {
            // early return
            return fragment;
        }

        if record {
            self.record_translated_fragment(fragment.clone());
        }
        format!("<rust>{}</rust>", fragment)
    }

    pub fn get_rust_funcs_required_for_chunk(&self) -> Vec<&str> {
        let mut ret = Vec::new();
        // module imports
        if self.found_sed.get() {
            ret.push("module_regex");
        }
        if self.found_pkg_config.get() {
            ret.push("module_pkg_config");
        }
        // function definitions
        if self.found_redirection.get() {
            ret.push("write_file");
        }
        if self.found_define.get() {
            ret.push("define_cfg");
            ret.push("define_env");
        }
        if self.found_pkg_config.get() {
            ret.push("pkg_config");
        }
        if self.found_check_header.get() {
            ret.push("check_header");
        }
        if self.found_check_library.get() {
            ret.push("check_library");
        }
        if self.found_check_decl.get() {
            ret.push("check_decl");
        }
        ret
    }

    pub fn get_embedded_chunks(&self) -> HashMap<ChunkId, String> {
        self.embedded_chunks.borrow().clone()
    }

    pub fn get_tab_width() -> usize {
        Self::TAB_WIDTH
    }
}

impl<'a> DisplayNode for TranslatingPrinter<'a> {
    type Word = AcWord;

    fn display_node(&self, node_id: NodeId, indent_level: usize) -> String {
        if let Some(node) = self.get_node(node_id) {
            let is_top = self.top_most.get().is_none();
            if is_top {
                self.top_most.replace(Some(node_id));
            } else if node.info.is_top_node() {
                let chunk_id = node.info.chunk_id.unwrap();
                if self.embedded_chunks.borrow().contains_key(&chunk_id) {
                    return "".into();
                } else {
                    let tab = " ".repeat(indent_level * Self::TAB_WIDTH);

                    // Check if we have a inlined translation for this chunk
                    if let Some(inlined_translation) = self.inlined_translations.get(&chunk_id) {
                        // Inline the inlined translation directly
                        self.embedded_chunks
                            .borrow_mut()
                            .insert(chunk_id, "inlined".to_string());

                        let inlined_code = inlined_translation
                            .inline_rust_code
                            .iter()
                            .map(|line| format!("{tab}{}", line))
                            .collect::<Vec<_>>()
                            .join("\n");
                        return format!("{}", self.enclose_by_rust_tags(inlined_code, true));
                    } else {
                        // Fall back to function call for LLM-translated chunks
                        let func_name = super::rust_func_placeholder_name(chunk_id);
                        self.embedded_chunks
                            .borrow_mut()
                            .insert(chunk_id, func_name.clone());

                        let call_site = self
                            .analyzer
                            .print_chunk_skeleton_call_site(chunk_id, &func_name);
                        return format!("{tab}{}", self.enclose_by_rust_tags(call_site, true));
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
            if is_top {
                self.top_most.replace(None);
            }
            result
        } else {
            String::new()
        }
    }

    fn display_word(&self, word: &AcWord, should_quote: bool) -> String {
        use autotools_parser::ast::minimal::Word::*;
        use autotools_parser::ast::minimal::WordFragment::{DoubleQuoted, Literal};
        match &word.0 {
            Empty => "".to_string(),
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
            DictionaryValue::Var(name) => format!("${{{}}}", name),
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
        let printed_keys = match num_keys {
            1 => keys.first().unwrap().clone(),
            _ => format!("({})", keys.join(", ")),
        };
        let operation = match num_keys {
            1 => format!("{}.get({})", dict_name, printed_keys),
            _ => format!("{}.get(&{})", dict_name, printed_keys),
        };
        operation
    }

    fn display_dictionary_write(
        &self,
        dict_name: &str,
        access: &DictionaryAccess,
        value_type: &DataType,
        value: &str,
    ) -> String {
        debug_assert_eq!(access.operation, DictionaryOperation::Write);
        let keys = access
            .keys
            .iter()
            .map(|key| key.print())
            .collect::<Vec<_>>();
        let num_keys = keys.len();
        let printed_keys = match num_keys {
            1 => keys.first().unwrap().clone(),
            _ => format!("({})", keys.join(", ")),
        };

        self.record_translated_fragment(dict_name.to_owned());
        self.record_translated_fragment(printed_keys.to_owned());
        let operation = match value_type {
            DataType::List(_) => format!("{}.entry({})", dict_name, printed_keys),
            _ => format!("{}.insert({},", dict_name, printed_keys),
        };
        let lhs = self.enclose_by_rust_tags(operation, false);
        let rhs = match value_type {
            DataType::List(_) => {
                let list = format!(
                    "[{}]",
                    value
                        .split_whitespace()
                        .map(|s| format!("\"{s}\".to_string()"))
                        .join(", ")
                );
                self.enclose_by_rust_tags(list, false)
            }
            _ => value.to_owned(),
        };
        format!("{}=\"{}\"", lhs, rhs)
    }

    fn display_cfg_atom(&self, atom: &Atom, negated: bool) -> String {
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
                                .query_conditional_compilation_migration_policy(&option_name)
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
                                .query_conditional_compilation_migration_policy(&option_name)
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
                                .query_conditional_compilation_migration_policy(&option_name)
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
                VarCond::True => may_negate(name.into(), false ^ negated),
                VarCond::False => may_negate(name.into(), true ^ negated),
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
        match guard {
            Guard::N(negated, atom) => {
                if should_atom_replaced(atom) {
                    let cfg_atom_str = self.display_cfg_atom(atom, *negated);
                    let cfg_str = format!("cfg!({})", cfg_atom_str);
                    self.enclose_by_rust_tags(cfg_str, true)
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
                if self.full_rust_mode {
                    format!("({})", guards_str)
                } else {
                    guards_str
                }
            }
            Guard::And(guards) => {
                let guards_str = guards
                    .iter()
                    .map(|guard| self.display_guard(guard))
                    .join(" && ");
                if self.full_rust_mode {
                    format!("({})", guards_str)
                } else {
                    guards_str
                }
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

    fn display_word_as_format_string(&self, word: &AcWord) -> String {
        let (format_string, vars) = self.take_format_string_and_vars(word);
        if vars.is_empty() {
            format!("\"{format_string}\".to_string()")
        } else {
            format!(
                "format!(\"{}\", {})",
                format_string,
                vars.into_iter().join(", ")
            )
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
        let format_string = Self::escape_rust_string(&word);
        self.record_translated_fragment(format_string.clone());
        (format_string, vars)
    }

    fn escape_rust_string(s: &str) -> String {
        s.chars()
            .map(|c| match c {
                '"' => "\\\"".to_string(),
                '\\' => "\\\\".to_string(),
                '\n' => "\\n".to_string(),
                '\r' => "\\r".to_string(),
                '\t' => "\\t".to_string(),
                '\0' => "\\0".to_string(),
                c if c.is_control() => format!("\\u{{{:04x}}}", c as u32),
                c => c.to_string(),
            })
            .collect()
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
                    self.found_define.replace(true);
                    format!("define_cfg({:?}, {:?})", key, value)
                }
                CCMigrationType::Env => {
                    let key = policy.key.as_ref().unwrap();
                    self.found_define.replace(true);
                    format!("define_env({:?}, {:?})", key, value.unwrap_or_default())
                }
                _ => return "".into(),
            }
        } else {
            self.found_define.replace(true);
            format!("define_cfg({:?}, {:?})", key, value)
        };
        self.record_translated_fragment(define_call.clone());
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
            "{}" => Some(format!("&{}", vars_in_value.first().unwrap())),
            _ => Some(format!(
                "&format!(\"{}\", {})",
                value_fstr,
                vars_in_value
                    .iter()
                    .map(|var| "&".to_owned() + var)
                    .join(",")
            )),
        };
        if vars_in_key.len() > 0 {
            if vars_in_value.len() > 0 {
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
            self.found_define.replace(true);
            let define_call = format!("define_cfg({}, {})", format_key, format_value);
            self.record_translated_fragment(define_call.clone());
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
                        self.found_define.replace(true);
                        format!("define_cfg({:?}, {})", key_fstr, format_value)
                    }
                    CCMigrationType::Env => {
                        self.found_define.replace(true);
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
                self.found_define.replace(true);
                format!("define_cfg({:?}, {})", key_fstr, format_value)
            };
            self.record_translated_fragment(define_call.clone());
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
        defines: &[String],
    ) -> String {
        self.found_check_header.replace(true);
        let tab = " ".repeat(indent_level * Self::TAB_WIDTH);
        let hint = if defines.is_empty() {
            Default::default()
        } else {
            format!(
                "{tab}# NOTE: You MUST insert: {} somewhere below\n",
                defines.join(", ")
            )
        };
        let mut ret = hint;
        for header in headers {
            let check_header = self.enclose_by_rust_tags(
                format!("check_header(\"{}\", {:?}, &CPPFLAGS)", header, includes),
                false,
            );
            let action_if_found = action_if_found
                .map(|cmds| self.display_body(cmds, indent_level + 1))
                .unwrap_or_default();
            let action_if_not_found = action_if_not_found
                .map(|cmds| self.display_body(cmds, indent_level + 1))
                .unwrap_or_default();

            ret.push_str(&format!(
                "{tab}if {} {{\n{}{tab}}}{}",
                check_header,
                action_if_found,
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
        defines: &[String],
    ) -> String {
        self.found_check_library.replace(true);
        let tab = " ".repeat(indent_level * Self::TAB_WIDTH);
        let tab_1 = " ".repeat((indent_level + 1) * Self::TAB_WIDTH);

        let mut ret = String::new();
        let func_call = format!(
            "check_library(\"{}\", &{:?}, &{:?}, &LDFLAGS, {:?})",
            func, libs, other_libs, try_std
        );
        self.record_translated_fragment(func_call.clone());
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
                    .iter()
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
        defines: &[String],
    ) -> String {
        self.found_check_decl.replace(true);
        let tab = " ".repeat(indent_level * Self::TAB_WIDTH);
        let tab_1 = " ".repeat((indent_level + 1) * Self::TAB_WIDTH);
        let hint = if defines.is_empty() {
            Default::default()
        } else {
            format!(
                "{tab}# NOTE: You MUST insert: {} somewhere below\n",
                defines.join(", ")
            )
        };
        let mut ret = hint;
        for symbol in symbols {
            let check_decl = self.enclose_by_rust_tags(
                format!("check_decl(\"{}\", {:?}, &CPPFLAGS)", symbol, includes),
                false,
            );
            let action_if_found = action_if_found
                .map(|cmds| self.display_body(cmds, indent_level + 1))
                .unwrap_or_default();
            let action_if_not_found = action_if_not_found
                .map(|cmds| self.display_body(cmds, indent_level + 1))
                .unwrap_or_default();
            ret.push_str(&format!(
                "{tab}if {} {{\n{}{tab}}}{}",
                check_decl,
                action_if_found,
                if action_if_not_found.is_empty() {
                    Default::default()
                } else {
                    format!(" else {{\n{action_if_not_found}{tab}}}")
                },
            ));
        }
        ret
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
                self.found_pkg_config.replace(true);
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

impl<'a> NodePool<AcWord> for TranslatingPrinter<'a> {
    fn display_shell_word(&self, shell_word: &WordFragment<AcWord>) -> String {
        if self.in_format_string.get() {
            if let WordFragment::Param(Parameter::Var(var)) = shell_word {
                self.formatted_vars.borrow_mut().push(var.to_owned());
                return "{}".into();
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
        let rhs = self.display_word(word, false);
        let loc = self.take_location();
        if let Some((dict_name, access, value_type)) = self.dict_accesses.get(&loc) {
            format!(
                "{tab}{}",
                self.display_dictionary_write(dict_name, access, value_type, &rhs)
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
        let should_replace_with_ifelse = guards.iter().all(|guard| should_guard_replaced(guard));
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
                            let rhs = if let Some(vals) = &access.assigned_value {
                                vals.iter()
                                    .map(|v| self.display_dictionary_value(v))
                                    .collect::<String>()
                            } else {
                                String::new()
                            };
                            return self
                                .display_dictionary_write(dict_name, access, value_type, &rhs);
                        }
                        DictionaryOperation::Read => {
                            let lhs = access.assigned_to.clone().unwrap();
                            let rhs = self.enclose_by_rust_tags(
                                self.display_dictionary_read(dict_name, access, value_type),
                                true,
                            );
                            return format!("{tab}{}={}", lhs, rhs);
                        }
                    }
                }
            }
            if as_shell(first)
                .and_then(as_literal)
                .is_some_and(|cmd| cmd == "sed")
            {
                self.found_sed.replace(true);
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
            self.found_redirection.replace(true);
        }
        let tab = " ".repeat(indent_level * Self::TAB_WIDTH);
        if redirects.len() == 2 {
            if let (Redirect::Write(_, file), Redirect::Heredoc(_, heredoc)) =
                (&redirects[0], &redirects[1])
            {
                if let Word::Single(MayM4::Shell(WordFragment::Literal(filename))) = &file.0 {
                    let rust_string = {
                        let path = format!("Path::new(\"{}\")", filename);
                        self.record_translated_fragment(path.clone());
                        let content = self.display_word_as_format_string(heredoc);
                        self.enclose_by_rust_tags(
                            format!("write_file({}, &{})", path, content),
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

impl<'a> DisplayM4 for TranslatingPrinter<'a> {
    fn display_m4_macro(&self, m4_macro: &M4Macro, indent_level: usize) -> String {
        let tab = " ".repeat(indent_level * Self::M4_TAB_WIDTH);
        let node_id = self.node_cursor.get().unwrap();
        if let Some(effects) = self
            .analyzer
            .side_effects_of_frozen_macros
            .as_ref()
            .unwrap()
            .get(&node_id)
        {
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
        let mut required_defines: Vec<String> = Vec::new();

        if let Some(effects) = &m4_macro.effects {
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
                                self.record_translated_fragment(key.into());
                                self.found_define.replace(true);
                                required_defines
                                    .push(format!("define_cfg({:?}, {:?})", key, policy.value));
                            }
                            CCMigrationType::Env => {
                                let key = policy.key.as_ref().unwrap();
                                self.record_translated_fragment(key.into());
                                self.found_define.replace(true);
                                required_defines.push(format!(
                                    "define_env({:?}, {:?})",
                                    key,
                                    policy.value.clone().unwrap_or_default()
                                ));
                            }
                            _ => (),
                        }
                    }
                }
            }
        }

        match m4_macro.name.as_str() {
            "AC_INIT" => {
                format!(
                    "{tab}# Sample translation of AC_INIT\n{}",
                    get_function_body_ac_init()
                )
            }
            "AC_CACHE_CHECK" => {
                let description = m4_macro.get_arg_as_literal(0).unwrap();
                let body = m4_macro.get_arg_as_cmd(2).unwrap();
                format!(
                    "{tab}# Check {description}\n{}",
                    self.display_body(&body, indent_level)
                )
            }
            "AC_DEFINE" => {
                let key = match m4_macro.args.get(0).unwrap() {
                    M4Argument::Word(word) => self.display_word(word, false),
                    M4Argument::Literal(lit) => lit.to_owned(),
                    _ => unreachable!(),
                };
                let value = m4_macro.get_arg_as_literal(1).unwrap_or_default();
                let ret = self.display_ac_define(&key, &value);
                format!("{tab}{}", self.enclose_by_rust_tags(ret, false))
            }
            "AC_DEFINE_UNQUOTED" => {
                let key = match m4_macro.args.get(0).unwrap() {
                    M4Argument::Word(word) => word,
                    M4Argument::Literal(lit) => &(lit.clone().into()),
                    _ => unreachable!(),
                };
                let value = match m4_macro.args.get(1) {
                    Some(M4Argument::Word(word)) => Some(word),
                    Some(M4Argument::Literal(lit)) => Some(&(lit.clone().into())),
                    None => None,
                    _ => unreachable!(),
                };
                let ret = self.display_ac_define_unquoted(key, value);
                format!("{tab}{}", self.enclose_by_rust_tags(ret, false))
            }
            "AC_CHECK_HEADER" => {
                let header = match m4_macro.args.get(0).unwrap() {
                    M4Argument::Word(word) => self.display_word(word, false),
                    M4Argument::Literal(lit) => lit.clone().into(),
                    _ => unreachable!(),
                };
                let action_if_found = m4_macro.get_arg_as_cmd(1);
                let action_if_not_found = m4_macro.get_arg_as_cmd(2);
                let includes = m4_macro.get_arg_as_program(3).unwrap_or_default();
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
                let headers = m4_macro
                    .get_arg_as_array(0)
                    .unwrap_or_default()
                    .into_iter()
                    .map(|word| self.display_word(&word, false))
                    .collect::<Vec<_>>();
                let action_if_found = m4_macro.get_arg_as_cmd(1);
                let action_if_not_found = m4_macro.get_arg_as_cmd(2);
                let includes = m4_macro.get_arg_as_program(3).unwrap_or_default();
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
                let library = match m4_macro.args.get(0).unwrap() {
                    M4Argument::Word(word) => self.display_word(word, false),
                    M4Argument::Literal(lit) => lit.clone().into(),
                    _ => unreachable!(),
                };
                let function = match m4_macro.args.get(1).unwrap() {
                    M4Argument::Word(word) => self.display_word(word, false),
                    M4Argument::Literal(lit) => lit.clone().into(),
                    _ => unreachable!(),
                };
                let action_if_found = m4_macro.get_arg_as_cmd(2);
                let action_if_not_found = m4_macro.get_arg_as_cmd(3);
                let other_libs = m4_macro
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
                let function = match m4_macro.args.get(0).unwrap() {
                    M4Argument::Word(word) => self.display_word(word, false),
                    M4Argument::Literal(lit) => lit.clone().into(),
                    _ => unreachable!(),
                };
                let libraries = m4_macro
                    .get_arg_as_array(1)
                    .unwrap_or_default()
                    .into_iter()
                    .map(|word| self.display_word(&word, false))
                    .collect::<Vec<_>>();
                let action_if_found = m4_macro.get_arg_as_cmd(2);
                let action_if_not_found = m4_macro.get_arg_as_cmd(3);
                let other_libs = m4_macro
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
                let symbol = match m4_macro.args.get(0).unwrap() {
                    M4Argument::Word(word) => self.display_word(word, false),
                    M4Argument::Literal(lit) => lit.clone().into(),
                    _ => unreachable!(),
                };
                let action_if_found = m4_macro.get_arg_as_cmd(1);
                let action_if_not_found = m4_macro.get_arg_as_cmd(2);
                let includes = m4_macro.get_arg_as_program(3).unwrap_or_default();
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
                let symbols = m4_macro
                    .get_arg_as_array(0)
                    .unwrap_or_default()
                    .into_iter()
                    .map(|word| self.display_word(&word, false))
                    .collect::<Vec<_>>();
                let action_if_found = m4_macro.get_arg_as_cmd(1);
                let action_if_not_found = m4_macro.get_arg_as_cmd(2);
                let includes = m4_macro.get_arg_as_program(3).unwrap_or_default();
                self.display_ac_check_decls(
                    indent_level,
                    &symbols,
                    action_if_found.as_ref(),
                    action_if_not_found.as_ref(),
                    &includes,
                    &required_defines,
                )
            }
            "PKG_CHECK_MODULES" => self.display_pkg_check_modules(node_id, indent_level),
            _ => {
                // Add hint comment for LLM guidance when CPP symbols need define_cfg/define_env
                let macro_output = self.m4_macro_to_string(m4_macro, indent_level);
                if !required_defines.is_empty() {
                    for req_def in &required_defines {
                        self.record_translated_fragment(req_def.clone());
                    }
                    let hint = format!(
                        "{tab}# NOTE: You MUST include: {}\n",
                        required_defines.join(", ")
                    );
                    format!("{}{}", hint, macro_output)
                } else {
                    macro_output
                }
            }
        }
    }
}

fn should_guard_replaced(guard: &Guard) -> bool {
    match guard {
        Guard::N(_, atom) => should_atom_replaced(atom),
        Guard::Or(guards) | Guard::And(guards) => guards.iter().any(should_guard_replaced),
    }
}

fn should_atom_replaced(atom: &Atom) -> bool {
    use Atom::*;
    match atom {
        Arch(_) | Cpu(_) | Os(_) | Env(_) | Abi(_) | Arg(_, _) => true,
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_escape_rust_string() {
        // Test basic strings
        assert_eq!(TranslatingPrinter::escape_rust_string("hello"), "hello");

        // Test special characters that need escaping
        assert_eq!(
            TranslatingPrinter::escape_rust_string("hello\tworld"),
            "hello\\tworld"
        );
        assert_eq!(
            TranslatingPrinter::escape_rust_string("hello\nworld"),
            "hello\\nworld"
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

        // Test a complex example with multiple special characters
        assert_eq!(
            TranslatingPrinter::escape_rust_string("\thi\n\"test\"\r\\path"),
            "\\thi\\n\\\"test\\\"\\r\\\\path"
        );
    }
}
