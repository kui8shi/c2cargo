use std::{
    collections::{HashMap, HashSet},
    path::PathBuf,
};

use autotools_parser::{
    ast::{node::AcCommand, MayM4},
    m4_macro::{M4Argument, Var, VarAttrs, CPP, MACROS},
};
use regex::Regex;

use crate::analyzer::{as_literal, as_shell};

use super::{Analyzer, AstVisitor, M4Macro, Node, NodeId, ShellCommand};

mod macros_list;

/// Represent side effects of fixed macros
#[derive(Debug, Default, Clone)]
pub(super) struct FixedMacroSideEffect {
    /// name of the macro
    pub macro_name: String,
    /// shell variables
    pub vars: HashMap<String, (VarAttrs, String)>,
    /// cpp symbols
    pub cpps: HashMap<String, Option<String>>,
}

/// Visitor to find case statements branching given variables.
#[derive(Debug)]
pub(super) struct MacroFinder<'a> {
    analyzer: &'a mut Analyzer,
    cursor: Option<NodeId>,
    /// Collected case branches where the variable branches one of `var_names`.
    found_macro_calls: Vec<(NodeId, M4Macro)>,
}

impl<'a> MacroFinder<'a> {
    pub fn find_macro_calls(analyzer: &'a mut Analyzer) -> HashMap<String, Vec<(NodeId, M4Macro)>> {
        let mut s = Self {
            analyzer,
            cursor: None,
            found_macro_calls: Vec::new(),
        };

        let mut remove_nodes = HashSet::new();
        let mut called: HashMap<String, Vec<(NodeId, M4Macro)>> = Default::default();
        let mut oneshot_calls = HashSet::new();
        for (order, id) in s.analyzer.get_top_ids().into_iter().enumerate() {
            s.visit_top(id);
            for (id, macro_call) in s.found_macro_calls.drain(..) {
                if let Some(sig) = macro_call.signature.as_ref() {
                    if sig.is_oneshot {
                        let name = macro_call.name.as_str();
                        if !oneshot_calls.contains(name) {
                            oneshot_calls.insert(name.to_owned());
                        } else {
                            // oneshot macro calls are ignored after the second time
                            remove_nodes.insert(id);
                            continue;
                        }
                    }
                    if let Some(required) = sig.require.as_ref() {
                        for name in required {
                            if !called.contains_key(name) {
                                let required_sig = MACROS.get(name).unwrap();
                                if required_sig.is_oneshot {
                                    oneshot_calls.insert(name.to_owned());
                                }
                                let effects =
                                    (!required_sig.has_no_exports()).then_some(required_sig.into());
                                let required_call = M4Macro::new_with_side_effect(
                                    name.to_owned(),
                                    Vec::new(),
                                    effects,
                                    None,
                                );
                                let new_id = s.analyzer.pool.nodes.insert(Node {
                                    comment: None,
                                    range: s.analyzer.get_ranges(id).unwrap().to_vec(),
                                    cmd: AcCommand(MayM4::Macro(required_call.clone())),
                                    // FIXME: this brace's block id is strage
                                    info: Default::default(),
                                });
                                s.analyzer.top_ids.insert(order, new_id);
                                called
                                    .entry(name.to_owned())
                                    .or_default()
                                    .push((new_id, required_call));
                            }
                        }
                    }
                }
                called
                    .entry(macro_call.name.to_owned())
                    .or_default()
                    .push((id, macro_call));
            }
        }

        for id in remove_nodes {
            s.analyzer.remove_node(id);
        }
        called
    }
}

impl Analyzer {
    pub(super) fn find_macro_calls(&mut self) {
        let macro_calls = MacroFinder::find_macro_calls(self);
        self.macro_calls.replace(macro_calls);
        self.consume_error_macros();
        self.consume_m4sh_internal_macros();
        self.consume_autoconf_internal_macros();
        self.consume_notice_macros();
        self.consume_msg_only_macros();
        self.consume_config_macros();
        self.consume_subst_macros();
        self.consume_prereq_macros();
        self.consume_arg_macros();
        self.consume_cpp_macros();
        self.consume_ac_init_macro();
    }
}

impl Analyzer {
    fn consume_error_macros(&mut self) {
        let macro_calls = self.macro_calls.as_ref().unwrap();
        if let Some(v) = macro_calls.get("AX_PREFIX_CONFIG_H") {
            if let Some((_id, m4_macro)) = v.first() {
                if let Some(lit) = m4_macro.get_arg_as_literal(1) {
                    self.cpp_prefix.replace(lit + "_");
                }
            }
        }

        for error_macro in ["AC_MSG_ERROR"] {
            if let Some(v) = macro_calls.get(error_macro) {
                for (node_id, _) in v {
                    if let Some(block_id) = self.get_node(*node_id).unwrap().info.block {
                        self.blocks[block_id].error_out = true;
                    }
                }
            }
        }
    }

    fn consume_m4sh_internal_macros(&mut self) {
        let mut remove_nodes = HashSet::new();
        let macro_calls = self.macro_calls.as_ref().unwrap();
        for m4sh_internal_macro in ["AS_INIT", "AS_ME_PREPARE", "AS_UNAME"] {
            if let Some(v) = macro_calls.get(m4sh_internal_macro) {
                for (node_id, _) in v {
                    remove_nodes.insert(*node_id);
                }
            }
        }

        for id in remove_nodes {
            self.remove_node(id);
        }
    }

    fn consume_autoconf_internal_macros(&mut self) {
        let mut remove_nodes = HashSet::new();
        let macro_calls = self.macro_calls.as_ref().unwrap();
        for autoconf_internal_macro in ["AC_CONFIG_SRCDIR"] {
            if let Some(v) = macro_calls.get(autoconf_internal_macro) {
                for (node_id, _) in v {
                    remove_nodes.insert(*node_id);
                }
            }
        }

        for id in remove_nodes {
            self.remove_node(id);
        }
    }

    fn consume_notice_macros(&mut self) {
        let mut remove_nodes = HashSet::new();
        let macro_calls = self.macro_calls.as_ref().unwrap();
        for notice_macro in ["AC_PREREQ", "AC_COPYRIGHT", "AC_REVISION", "AH_TOP"] {
            if let Some(v) = macro_calls.get(notice_macro) {
                for (node_id, _) in v {
                    remove_nodes.insert(*node_id);
                }
            }
        }

        for id in remove_nodes {
            self.remove_node(id);
        }
    }

    fn consume_msg_only_macros(&mut self) {
        let mut remove_nodes = HashSet::new();
        let macro_calls = self.macro_calls.as_ref().unwrap();
        for msg_only_macro in ["AC_MSG_CHECKING", "AC_MSG_RESULT", "AC_MSG_NOTICE"] {
            if let Some(v) = macro_calls.get(msg_only_macro) {
                for (node_id, _) in v {
                    remove_nodes.insert(*node_id);
                }
            }
        }

        for id in remove_nodes {
            self.remove_node(id);
        }
    }

    fn consume_config_macros(&mut self) {
        let mut remove_nodes = HashSet::new();
        let macro_calls = self.macro_calls.as_ref().unwrap();

        for config_macro in ["AC_CONFIG_HEADERS"] {
            if let Some(v) = macro_calls.get(config_macro) {
                for (node_id, macro_call) in v {
                    if let Some(tags) = macro_call
                        .effects
                        .as_ref()
                        .and_then(|side_effects| side_effects.tags.as_ref())
                    {
                        for (dst, src) in tags {
                            let dst = PathBuf::from(dst);
                            let src = if let Some(src) = src {
                                PathBuf::from(src)
                            } else {
                                let mut path = dst.clone();
                                path.add_extension("in");
                                path
                            };
                            if src.exists() {
                                self.project_info.config_files.push((dst, src));
                            }
                        }
                    }
                    remove_nodes.insert(*node_id);
                }
            }
        }

        for subst_macro in ["AC_CONFIG_FILES", "AC_OUTPUT"] {
            if let Some(v) = macro_calls.get(subst_macro) {
                for (node_id, macro_call) in v {
                    if let Some(tags) = macro_call
                        .effects
                        .as_ref()
                        .and_then(|side_effects| side_effects.tags.as_ref())
                    {
                        for (dst, src) in tags {
                            let mut is_automake = false;
                            let dst = PathBuf::from(dst);
                            let src = if let Some(src) = src {
                                PathBuf::from(src)
                            } else {
                                let mut path = dst.clone();
                                if path.ends_with("Makefile") {
                                    path.add_extension("am");
                                    is_automake = true;
                                } else {
                                    path.add_extension("in");
                                }
                                path
                            };
                            if src.exists() {
                                if is_automake {
                                    self.project_info.am_files.push(src.clone());
                                }
                                self.project_info.subst_files.push((dst, src));
                            }
                        }
                    }
                    remove_nodes.insert(*node_id);
                }
            }
        }

        for id in remove_nodes {
            self.remove_node(id);
        }
    }

    fn consume_subst_macros(&mut self) {
        let mut remove_nodes = HashSet::new();
        let macro_calls = self.macro_calls.as_ref().unwrap();
        for subst_macro in ["AC_SUBST", "AM_SUBST_NOTMAKE"] {
            for (id, macro_call) in macro_calls.get(subst_macro).cloned().into_iter().flatten() {
                if macro_call.args.len() > 1 {
                    let name = macro_call.get_arg_as_literal(0).unwrap();
                    let word = macro_call.get_arg_as_word(1).unwrap();
                    // replace substitution command with assignment
                    self.pool.nodes[id].cmd = ShellCommand::Assignment(name.clone(), word).into();
                } else {
                    remove_nodes.insert(id);
                }
            }
        }

        for id in remove_nodes {
            self.remove_node(id);
        }
    }

    fn consume_prereq_macros(&mut self) {
        let mut remove_nodes = HashSet::new();
        let macro_calls = self.macro_calls.as_ref().unwrap();
        for prereq_macro in ["AC_PREREQ"] {
            for (id, _) in macro_calls.get(prereq_macro).cloned().into_iter().flatten() {
                remove_nodes.insert(id);
            }
        }

        for id in remove_nodes {
            self.remove_node(id);
        }
    }

    fn consume_arg_macros(&mut self) {
        let mut remove_nodes = HashSet::new();
        let macro_calls = self.macro_calls.as_ref().unwrap();
        for arg_macro in ["AC_ARG_VAR"] {
            for (id, _) in macro_calls.get(arg_macro).cloned().into_iter().flatten() {
                remove_nodes.insert(id);
            }
        }

        for id in remove_nodes {
            self.remove_node(id);
        }
    }

    fn consume_cpp_macros(&mut self) {
        let mut remove_nodes = HashSet::new();
        let mut cpp_defs = HashSet::new();
        let macro_calls = self.macro_calls.as_ref().unwrap();

        for cpp_verbatim_macro in ["AH_VERBATIM"] {
            for (id, macro_call) in macro_calls
                .get(cpp_verbatim_macro)
                .cloned()
                .into_iter()
                .flatten()
            {
                let template = macro_call.get_arg_as_program(1).unwrap();
                let undef_re = Regex::new(r"^#undef\s+(?<key>[A-Z0-9_]+)").unwrap();
                for cap in undef_re.captures_iter(&template) {
                    let key = cap.name("key").unwrap().as_str().to_string();
                    cpp_defs.insert(key);
                }
                remove_nodes.insert(id);
            }
        }

        for cpp_template_macro in ["AH_TEMPLATE"] {
            for (id, macro_call) in macro_calls
                .get(cpp_template_macro)
                .cloned()
                .into_iter()
                .flatten()
            {
                let key = macro_call.get_arg_as_literal(0).unwrap();
                cpp_defs.insert(key);
                remove_nodes.insert(id);
            }
        }

        for cpp_define_macro in ["AC_DEFINE", "AC_DEFINE_UNQUOTED"] {
            for (_, macro_call) in macro_calls
                .get(cpp_define_macro)
                .cloned()
                .into_iter()
                .flatten()
            {
                let key = match macro_call.args.first() {
                    Some(M4Argument::Word(word)) => {
                        if let Some(lit) = as_shell(word).and_then(as_literal) {
                            lit.to_owned()
                        } else {
                            continue;
                        }
                    }
                    Some(M4Argument::Literal(lit)) => lit.clone(),
                    _ => unreachable!(),
                };
                cpp_defs.insert(key);
            }
        }

        for id in remove_nodes {
            self.remove_node(id);
        }

        self.cpp_defs.replace(cpp_defs);
    }

    fn consume_ac_init_macro(&mut self) {
        let macro_calls = self.macro_calls.as_ref().unwrap();

        if let Some(v) = macro_calls.get("AC_INIT") {
            for (_, macro_call) in v {
                let mut metadata = super::ProjectMetadata::default();

                // AC_INIT([package-name], [version], [bug-report], [tarname], [url])
                if let Some(name) = macro_call.get_arg_as_literal(0) {
                    let rust_name = name
                        .chars()
                        .map(|c| {
                            if c.is_alphanumeric() || c == '-' || c == '_' {
                                c
                            } else {
                                '-'
                            }
                        })
                        .collect::<String>()
                        .to_lowercase();
                    metadata.name = Some(rust_name);
                }
                if let Some(version) = macro_call.get_arg_as_literal(1) {
                    metadata.version = Some(version);
                }
                if let Some(bug_report) = macro_call.get_arg_as_literal(2) {
                    metadata.bug_report = Some(bug_report);
                }
                if let Some(tarname) = macro_call.get_arg_as_literal(3) {
                    metadata.tarname = Some(tarname);
                }
                if let Some(url) = macro_call.get_arg_as_literal(4) {
                    metadata.url = Some(url);
                }

                self.project_metadata.replace(metadata);
                // Note: Don't remove AC_INIT nodes as they're needed for build.rs generation
            }
        }
    }

    pub(super) fn analyze_link_macros(&mut self) {
        let macro_calls = self.macro_calls.as_ref().unwrap();
        for ac_link_macro in ["AC_CONFIG_LINKS"] {
            for (id, macro_call) in macro_calls
                .get(ac_link_macro)
                .cloned()
                .into_iter()
                .flatten()
            {
                let loc = self.get_location_of_node_end(id);
                // due to the limitation of side effects description parsed in autoconf-parser,
                // we have to take pairs of paths from the macro argument.
                for word in macro_call.get_arg_as_array(0).unwrap() {
                    let value_exprs = self.vsa_inspect_word(&word, &loc, Some(':'));
                    if value_exprs.len() != 2 {
                        // exactly two value expressions (:paths) in an element required;
                        continue;
                    }
                    let from = self
                        .resolve_value_expression(&value_exprs[0], &loc, false)
                        .into_iter()
                        .map(PathBuf::from)
                        .collect::<Vec<_>>();
                    let to = self
                        .resolve_value_expression(&value_exprs[1], &loc, false)
                        .into_iter()
                        .map(PathBuf::from)
                        .filter(|path| self.project_info.project_dir.join(path).exists())
                        .collect::<Vec<_>>();
                    self.project_info.dynamic_links.push((from, to));
                }
            }
        }
    }

    pub(super) fn consume_automake_macros(&mut self) {
        let mut remove_nodes = HashSet::new();
        let macro_calls = self.macro_calls.as_ref().unwrap();
        // Actually there are few macros that export am conditional implicitly.
        // (e.g. PKG_WITH_MODULES)
        // But we won't cover them for now.
        let mut am_cond_to_guard = HashMap::new();
        for am_cond_macro in ["AM_CONDITIONAL"] {
            for (id, macro_call) in macro_calls
                .get(am_cond_macro)
                .cloned()
                .into_iter()
                .flatten()
            {
                let block_id = self.get_node(id).unwrap().info.branches.first().unwrap();
                let guard = self.get_block(*block_id).guards.last().unwrap();
                for am_cond_name in macro_call
                    .effects
                    .as_ref()
                    .iter()
                    .flat_map(|e| e.am_conds.iter().flatten())
                {
                    am_cond_to_guard.insert(am_cond_name.to_owned(), guard.clone());
                    //s.analyzer.automake
                }
                remove_nodes.insert(id);
            }
        }
        self.automake_mut().am_cond_to_guard = am_cond_to_guard;

        for id in remove_nodes {
            self.remove_node(id);
        }
    }

    // froze macros for legacy systems
    pub(super) fn froze_macros(&mut self) {
        let macro_calls = self.macro_calls.as_ref().unwrap();
        let mut side_effects_of_fixed_macros = HashMap::new();
        for legacy_compiler_macro in macros_list::MACROS_BLACKLIST {
            for (id, macro_call) in macro_calls
                .get(*legacy_compiler_macro)
                .cloned()
                .into_iter()
                .flatten()
            {
                if let Some(effects) = macro_call.effects {
                    let vars: Vec<&Var> = effects
                        .shell_vars
                        .iter()
                        .flat_map(|v| {
                            v.iter().filter(|var| var.is_defined()).filter(|var| {
                                self.is_var_used(var.name.as_str())
                                    || self.is_substituted(var.name.as_str())
                            })
                        })
                        .collect::<Vec<_>>();
                    let cpps: Vec<&CPP> = effects
                        .cpp_symbols
                        .iter()
                        .flat_map(|v| v.iter())
                        .collect::<Vec<_>>();
                    if vars.iter().all(|var| var.value.is_some())
                        && cpps.iter().all(|cpp| cpp.value.is_some())
                    {
                        let macro_name = macro_call.name.clone();
                        let vars = vars
                            .iter()
                            .map(|var| (var.name.clone(), (var.attrs, var.value.clone().unwrap())))
                            .collect::<HashMap<_, _>>();
                        let cpps = cpps
                            .iter()
                            .map(|cpp| (cpp.name.clone(), cpp.value.clone().unwrap()))
                            .collect::<HashMap<_, _>>();
                        side_effects_of_fixed_macros.insert(
                            id,
                            FixedMacroSideEffect {
                                macro_name,
                                vars,
                                cpps,
                            },
                        );
                    }
                }
            }
        }
        self.side_effects_of_frozen_macros
            .replace(side_effects_of_fixed_macros);
    }
}

impl Analyzer {
    pub(super) fn aggregate_cpp_defs(&mut self) {
        let cpp_defs = self
            .macro_calls
            .as_ref()
            .unwrap()
            .values()
            .flatten()
            .flat_map(|(_, m4_macro)| {
                m4_macro
                    .effects
                    .as_ref()
                    .and_then(|e| e.cpp_symbols.as_ref())
                    .into_iter()
                    .flatten()
                    .map(|sym| sym.name.clone())
            })
            .collect::<HashSet<String>>();
        self.cpp_defs.as_mut().unwrap().extend(cpp_defs);
    }

    pub(super) fn aggregate_subst_vars(&mut self) {
        let contents = self
            .project_info
            .subst_files
            .iter()
            .map(|(_, src)| {
                let bytes = std::fs::read(src).unwrap();
                String::from_utf8_lossy(&bytes).into_owned()
            })
            .collect::<Vec<_>>();
        let subst_vars = self
            .macro_calls
            .as_ref()
            .unwrap()
            .values()
            .flatten()
            .flat_map(|(_, m4_macro)| {
                m4_macro
                    .effects
                    .as_ref()
                    .and_then(|e| e.shell_vars.as_ref())
                    .map(|vars| {
                        vars.iter()
                            .filter_map(|var| var.is_output().then_some(var.name.to_owned()))
                    })
                    .into_iter()
                    .flatten()
            })
            .filter(|var_name| contents.iter().any(|c| c.contains(var_name)))
            .collect::<HashSet<String>>();
        self.subst_vars.replace(subst_vars);
    }

    pub(super) fn aggregate_input_vars(&mut self) {
        let input_vars = self
            .macro_calls
            .as_ref()
            .unwrap()
            .values()
            .flatten()
            .flat_map(|(_, m4_macro)| {
                m4_macro
                    .effects
                    .as_ref()
                    .and_then(|e| e.shell_vars.as_ref())
                    .map(|vars| {
                        vars.iter()
                            .filter_map(|var| var.is_input().then_some(var.name.to_owned()))
                    })
                    .into_iter()
                    .flatten()
            })
            .collect();
        self.input_vars.replace(input_vars);
    }

    pub(super) fn aggregate_env_vars(&mut self) {
        let env_vars = self
            .input_vars
            .as_ref()
            .unwrap()
            .iter()
            .filter(|&var_name| {
                self.get_scopes(var_name.as_str()).is_some_and(|scopes| {
                    scopes
                        .first()
                        .is_some_and(|s| s.owner.is_none() && s.bound_by.is_none())
                })
            })
            .cloned()
            .collect::<HashSet<String>>();
        self.env_vars.replace(env_vars);
    }
}

impl<'a> AstVisitor for MacroFinder<'a> {
    fn get_node(&self, node_id: NodeId) -> Option<&Node> {
        self.analyzer.get_node(node_id)
    }

    fn visit_top(&mut self, node_id: NodeId) {
        self.cursor.replace(node_id);
        self.walk_node(node_id);
    }

    fn visit_node(&mut self, node_id: NodeId) {
        if self.get_node(node_id).is_none() {
            return;
        }
        let saved_cursor = self.cursor.replace(node_id);

        if self
            .get_node(node_id)
            .is_some_and(|n| !n.info.is_top_node())
        {
            self.walk_node(node_id);
        }

        self.cursor = saved_cursor;
    }

    fn visit_m4_macro(&mut self, m4_macro: &M4Macro) {
        let node_id = self.cursor.unwrap();
        self.found_macro_calls.push((node_id, m4_macro.clone()));
        self.walk_m4_macro(m4_macro);
    }
}
