use std::{
    collections::{HashMap, HashSet},
    path::PathBuf,
};

use super::{as_literal, as_shell, Analyzer, AstVisitor, M4Macro, Node, NodeId};

/// Visitor to find case statements branching given variables.
#[derive(Debug)]
pub(super) struct MacroHandler<'a> {
    analyzer: &'a mut Analyzer,
    cursor: Option<NodeId>,
    /// Collected case branches where the variable branches one of `var_names`.
    pub found: HashMap<String, Vec<(NodeId, M4Macro)>>,
}

impl Analyzer {
    /// Find case statements matching the given variables in the top-level commands.
    pub fn find_macro_calls(&mut self) {
        MacroHandler::handle_macro_calls(self)
    }
}

impl<'a> MacroHandler<'a> {
    /// Create a new BranchFinder for the given variable names.
    pub fn handle_macro_calls(analyzer: &'a mut Analyzer) {
        let mut s = Self {
            analyzer,
            cursor: None,
            found: HashMap::new(),
        };
        for id in s.analyzer.get_top_ids() {
            s.visit_top(id);
        }
        if let Some(v) = s.found.get("AX_PREFIX_CONFIG_H") {
            if let Some((id, m4_macro)) = v.first().clone() {
                // prefix CPP vars
            }
        }

        s.analyzer.subst_vars = s
            .found
            .values()
            .flatten()
            .flat_map(|(id, m4_macro)| {
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
                s.analyzer
                    .project_info
                    .subst_files
                    .iter()
                    .any(|path| std::fs::read_to_string(path).unwrap().contains(var_name))
            })
            .collect::<HashSet<String>>();

        for subst_macro_name in ["AC_SUBST", "AM_SUBST_NOTMAKE"] {
            for (id, _) in s.found.get(subst_macro_name).into_iter().flatten() {
                s.analyzer.remove_node(*id);
            }
        }

        if let Some(v) = s.found.get("AC_CONFIG_FILES") {
            for (id, macro_call) in v {
                for word in macro_call.get_arg_as_array(0).unwrap() {
                    if let Some(lit) = as_shell(&word).and_then(as_literal) {
                        let path = {
                            let mut buf = PathBuf::from(lit);
                            if buf.ends_with("Makefile") {
                                buf.set_extension("am");
                            } else {
                                buf.set_extension("in");
                            }
                            s.analyzer.project_info.project_dir.join(buf)
                        };
                        if path.exists() {
                            s.analyzer.project_info.subst_files.push(path);
                        }
                    }
                }
                s.analyzer.remove_node(*id);
            }
        }

        s.analyzer.macro_calls = s.found
    }
}

impl<'a> AstVisitor for MacroHandler<'a> {
    fn get_node(&self, node_id: NodeId) -> &Node {
        self.analyzer.get_node(node_id)
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

    fn visit_m4_macro(&mut self, m4_macro: &M4Macro) {
        self.found
            .entry(m4_macro.name.to_owned())
            .or_default()
            .push((self.cursor.unwrap(), m4_macro.clone()));
        self.walk_m4_macro(m4_macro);
    }
}
