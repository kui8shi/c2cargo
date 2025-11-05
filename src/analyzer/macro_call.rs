use std::{
    collections::{HashMap, HashSet},
    path::PathBuf,
};

use autotools_parser::{
    ast::{node::AcCommand, MayM4},
    m4_macro,
};

use super::{Analyzer, AstVisitor, M4Macro, Node, NodeId, ShellCommand};

/// Visitor to find case statements branching given variables.
#[derive(Debug)]
pub(super) struct MacroHandler<'a> {
    analyzer: &'a mut Analyzer,
    cursor: Option<NodeId>,
    /// Collected case branches where the variable branches one of `var_names`.
    found_macro_calls: Vec<(NodeId, M4Macro)>,
}

impl<'a> MacroHandler<'a> {
    /// Create a new BranchFinder for the given variable names.
    pub fn handle_macro_calls(analyzer: &'a mut Analyzer) {
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
                                let required_sig = m4_macro::MACROS.get(name).unwrap();
                                if required_sig.is_oneshot {
                                    oneshot_calls.insert(name.to_owned());
                                }
                                let effects =
                                    (!required_sig.has_no_exports()).then_some(required_sig.into());
                                let required_call = m4_macro::M4Macro::new_with_side_effect(
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

        if let Some(v) = called.get("AX_PREFIX_CONFIG_H") {
            if let Some((_id, _m4_macro)) = v.first().clone() {
                // TODO: prefix CPP vars
            }
        }

        for error_macro in ["AC_MSG_ERROR"] {
            if let Some(v) = called.get(error_macro) {
                for (node_id, _) in v {
                    if let Some(block_id) = s.analyzer.get_node(*node_id).unwrap().info.block {
                        s.analyzer.blocks[block_id].error_out = true;
                    }
                }
            }
        }

        for msg_only_macro in ["AC_MSG_CHECKING", "AC_MSG_RESULT", "AC_MSG_NOTICE"] {
            if let Some(v) = called.get(msg_only_macro) {
                for (node_id, _) in v {
                    remove_nodes.insert(*node_id);
                }
            }
        }

        for instantiating_macro in ["AC_CONFIG_FILES", "AC_OUTPUT"] {
            if let Some(v) = called.get(instantiating_macro) {
                for (node_id, macro_call) in v {
                    if let Some(tags) = macro_call
                        .effects
                        .as_ref()
                        .map(|side_effects| side_effects.tags.as_ref())
                        .flatten()
                    {
                        for (dst, src) in tags {
                            let mut is_automake = false;
                            let path = if let Some(src) = src {
                                PathBuf::from(src)
                            } else {
                                let mut path = PathBuf::from(dst);
                                if path.ends_with("Makefile") {
                                    path.set_extension("am");
                                    is_automake = true;
                                } else {
                                    path.set_extension("in");
                                }
                                path
                            };
                            if path.exists() {
                                if is_automake {
                                    s.analyzer.project_info.am_files.push(path.clone());
                                } else {
                                    s.analyzer.project_info.subst_files.push(path.clone());
                                }
                            }
                        }
                    }
                    remove_nodes.insert(*node_id);
                }
            }
        }

        for subst_macro in ["AC_SUBST", "AM_SUBST_NOTMAKE"] {
            for (id, macro_call) in called.get(subst_macro).cloned().into_iter().flatten() {
                if macro_call.args.len() > 1 {
                    let name = macro_call.get_arg_as_literal(0).unwrap();
                    let word = macro_call.get_arg_as_word(1).unwrap();
                    let node = &mut s.analyzer.pool.nodes[id];
                    // replace substitution command with assignment
                    node.cmd = ShellCommand::Assignment(name.clone(), word).into();
                } else {
                    remove_nodes.insert(id);
                }
            }
        }

        for arg_macro in ["AC_ARG_VAR"] {
            for (id, _) in called.get(arg_macro).cloned().into_iter().flatten() {
                remove_nodes.insert(id);
            }
        }

        for cpp_macro in ["AH_VERBATIM"] {
            for (id, _) in called.get(cpp_macro).cloned().into_iter().flatten() {
                remove_nodes.insert(id);
            }
        }

        for id in remove_nodes {
            s.analyzer.remove_node(id);
        }

        s.analyzer.macro_calls.replace(called);
    }
}

impl Analyzer {
    pub(super) fn aggregate_subst_vars(&mut self) {
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
            .filter(|var_name| {
                self.project_info
                    .subst_files
                    .iter()
                    .chain(self.project_info.am_files.iter())
                    .any(|path| std::fs::read_to_string(path).unwrap().contains(var_name))
            })
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
            .cloned()
            .filter(|var_name| {
                self.get_scopes(var_name.as_str()).is_some_and(|scopes| {
                    scopes
                        .first()
                        .is_some_and(|s| s.owner.is_none() && s.bound_by.is_none())
                })
            })
            .collect::<HashSet<String>>();
        self.env_vars.replace(env_vars);
    }
}

impl<'a> AstVisitor for MacroHandler<'a> {
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
