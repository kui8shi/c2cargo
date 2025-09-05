use std::collections::{HashMap, HashSet};

use super::{
    guard::{Atom, Guard, VarCond, VoL},
    Analyzer, NodeId,
};
use crate::utils::glob::glob_enumerate;
use heck::ToSnakeCase;

mod llm_analysis;

/// doc
#[derive(Debug, Clone)]
struct BuildOption {
    decl_id: NodeId,
    option_name: String,
    vars: Vec<String>,
    candidates: Vec<String>,
    declaration: String,
    context: Vec<String>,
}

/// doc
#[derive(Debug, Clone, Default)]
pub(crate) struct BuildOptionInfo {
    build_options: HashMap<String, BuildOption>,
    decl_ids: HashSet<NodeId>,
    arg_var_to_option_name: HashMap<String, String>,
    dependencies: HashMap<String, HashSet<String>>,
}

impl Analyzer {
    /// Analyze various properties of build options using LLMs
    pub async fn analyze_build_options(&mut self) {
        self.build_option_info = self.extract_build_options();

        // we add information to guards that touch build options.
        self.convert_guards();

        // remove nodes related to disabling build options.
        // since cargo feature's additive nature, disabling build options is impossible.
        self.ignore_nodes_disabling_options();
        self.extract_dependencies_from_nodes_enabling_options();

        // collect informations for llm analysis
        self.collect_build_option_contexts();
        self.collect_build_option_value_candidates();

        // conduct llm analysis
        let results =
            llm_analysis::analyze_build_options(self.build_option_info.build_options.values())
                .await;

        for res in results {
            let build_option = self
                .build_option_info
                .build_options
                .get(&res.option_name)
                .unwrap();
            if res.representatives == vec!["no".to_owned(), "yes".to_owned()] {
                println!("{}: YesNo", res.option_name);
            } else {
                println!("{}: {:?}", res.option_name, res.representatives);
            }
            if let Some(aliases) = &res.aliases {
                println!("{}: Aliases: {:?}", res.option_name, aliases);
            }
        }
    }

    /// doc
    fn extract_build_options(&mut self) -> BuildOptionInfo {
        let mut ret = BuildOptionInfo::default();
        let mut target_macro_calls = Vec::new();
        for target_macro_name in ["AC_ARG_WITH", "AC_ARG_ENABLE"] {
            if let Some(v) = self.macro_calls.get(target_macro_name) {
                target_macro_calls.extend(v);
            }
        }
        for (node_id, m4_macro) in target_macro_calls {
            if let Some(option_name) = m4_macro.get_arg_as_literal(0) {
                let option_name = option_name.to_snake_case();
                let vars = self
                    .collect_variables(*node_id)
                    .0
                    .keys()
                    .filter_map(|name| match name.as_str() {
                        "withval" | "enableval" => None,
                        _ => Some(name.to_owned()),
                    })
                    .collect::<Vec<_>>();
                let build_option = BuildOption {
                    decl_id: *node_id,
                    option_name: option_name.clone(),
                    vars: vars.clone(),
                    candidates: Vec::new(),
                    declaration: String::new(),
                    context: Vec::new(),
                };
                ret.build_options.insert(option_name.clone(), build_option);
                ret.decl_ids.insert(*node_id);
                ret.decl_ids.extend(self.collect_descendant_nodes(*node_id));
                ret.arg_var_to_option_name
                    .extend(vars.into_iter().zip(std::iter::repeat(option_name.clone())));
            }
        }
        ret
    }

    fn convert_guards(&mut self) {
        let arg_vars = self
            .build_option_info
            .arg_var_to_option_name
            .keys()
            .map(|s| s.as_str())
            .collect::<HashSet<_>>();
        for (_, block) in self.blocks.iter_mut() {
            block.guards = block
                .guards
                .iter()
                .map(|guard| convert_guard_type_to_arg(&guard, &arg_vars))
                .collect();
        }
    }

    /// doc
    fn collect_build_option_contexts(&mut self) {
        let mut build_options = self
            .build_option_info
            .build_options
            .drain()
            .collect::<HashMap<_, _>>();
        let mut option_names_to_remove = HashSet::new();
        for build_option in build_options.values_mut() {
            build_option.declaration = self.display_node(build_option.decl_id);
            let mut target_vars = Vec::from(build_option.vars.clone());
            let mut visited = HashSet::new();
            while let Some(var) = target_vars.pop() {
                if !visited.contains(&var) {
                    visited.insert(var.clone());
                    for id in self.parent_nodes_of_blocks_guarded_by_variable(var.as_str()) {
                        let (defines, _) = self.collect_variables(id);
                        target_vars.extend(
                            defines
                                .keys()
                                .filter(|name| {
                                    name.to_lowercase()
                                        .contains(build_option.option_name.to_lowercase().as_str())
                                })
                                .cloned(),
                        );
                        build_option.context.push(self.display_node(id));
                    }
                }
            }
            if build_option.context.is_empty() {
                option_names_to_remove.insert(build_option.option_name.to_owned());
            }
        }

        for option_name in option_names_to_remove {
            // remove build options that have no side effects.
            build_options.remove(option_name.as_str());
        }

        self.build_option_info.build_options = build_options;
    }

    fn collect_build_option_value_candidates(&mut self) {
        let mut build_options = self
            .build_option_info
            .build_options
            .drain()
            .collect::<HashMap<_, _>>();
        for build_option in build_options.values_mut() {
            let mut values = HashSet::from(["yes".to_owned(), "no".to_owned()]);
            for id in self.collect_descendant_nodes(build_option.decl_id) {
                for &block_id in &self.get_node(id).info.child_blocks {
                    for guard in self.blocks[block_id].guards.iter() {
                        values.extend(enumerate_literal(guard));
                    }
                }
            }
            build_option.candidates = normalize(values.into_iter().collect());
        }
        self.build_option_info.build_options = build_options;
    }

    /// Remove nodes where a build option variable is set to "no".
    fn ignore_nodes_disabling_options(&mut self) {
        use crate::analyzer::{as_literal, as_shell, MayM4};
        use autotools_parser::ast::node::ShellCommand;

        let mut nodes_to_remove = Vec::new();

        // Find all assignment nodes where this variable is set to "no"
        for (node_id, node) in self
            .pool
            .nodes
            .iter()
            .filter(|(node_id, _)| !self.build_option_info.decl_ids.contains(node_id))
        {
            if let MayM4::Shell(ShellCommand::Assignment(lhs, rhs)) = &node.cmd.0 {
                // Check if this assignment is for our target variable
                if self
                    .build_option_info
                    .arg_var_to_option_name
                    .contains_key(lhs.as_str())
                {
                    // Check if the right-hand side is the literal "no"
                    if let Some(shell_word) = as_shell(rhs) {
                        if let Some(literal) = as_literal(shell_word) {
                            if literal == "no" {
                                nodes_to_remove.push(node_id);
                            }
                        }
                    }
                }
            }
        }

        // Remove the identified nodes
        for &node_id in &nodes_to_remove {
            self.remove_node(node_id);
        }
    }

    /// Extract dependencies from nodes where a build option variable is set to "yes".
    fn extract_dependencies_from_nodes_enabling_options(&mut self) {
        use crate::analyzer::{as_literal, as_shell, MayM4};
        use autotools_parser::ast::node::ShellCommand;

        let mut nodes_to_remove = Vec::new();

        // Find all assignment nodes where this variable is set to "no"
        for (node_id, node) in self
            .pool
            .nodes
            .iter()
            .filter(|(node_id, _)| !self.build_option_info.decl_ids.contains(node_id))
        {
            if let MayM4::Shell(ShellCommand::Assignment(lhs, rhs)) = &node.cmd.0 {
                // Check if this assignment is for our target variable
                if let Some(option_name) = self
                    .build_option_info
                    .arg_var_to_option_name
                    .get(lhs.as_str())
                {
                    // Check if the right-hand side is the literal "no"
                    if let Some(shell_word) = as_shell(rhs) {
                        if let Some(literal) = as_literal(shell_word) {
                            if literal == "yes" {
                                nodes_to_remove.push(node_id);
                                // check if the assign node is guarded by other arg vars.
                                if let Some(arg_var) = self
                                    .block_of_node(node_id)
                                    .map(|block| {
                                        block
                                            .guards
                                            .iter()
                                            .flat_map(|guard| match guard {
                                                Guard::N(false, Atom::Arg(name, VarCond::Yes))
                                                    if lhs.as_str() != name =>
                                                {
                                                    Some(name.to_owned())
                                                }
                                                _ => None,
                                            })
                                            .next()
                                    })
                                    .flatten()
                                {
                                    if let Some(dependent_option_name) =
                                        self.build_option_info.arg_var_to_option_name.get(&arg_var)
                                    {
                                        self.build_option_info
                                            .dependencies
                                            .entry(dependent_option_name.to_owned())
                                            .or_default()
                                            .insert(option_name.to_owned());
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        for node_id in nodes_to_remove {
            self.remove_node(node_id);
        }
    }
}

fn convert_guard_type_to_arg(guard: &Guard, arg_vars: &HashSet<&str>) -> Guard {
    match guard {
        Guard::N(negated, atom) => match atom {
            Atom::Var(name, cond) if arg_vars.contains(name.as_str()) => {
                Guard::N(negated.clone(), Atom::Arg(name.clone(), cond.clone()))
            }
            _ => guard.clone(),
        },
        Guard::And(v) => Guard::And(
            v.iter()
                .map(|g| convert_guard_type_to_arg(g, &arg_vars))
                .collect(),
        ),
        Guard::Or(v) => Guard::Or(
            v.iter()
                .map(|g| convert_guard_type_to_arg(g, &arg_vars))
                .collect(),
        ),
    }
}

fn enumerate_literal(guard: &Guard) -> Vec<String> {
    match guard {
        Guard::N(negated, Atom::Var(_, cond) | Atom::Arg(_, cond)) if !negated => match cond {
            VarCond::Yes => {
                vec!["yes".to_owned()]
            }
            VarCond::No => {
                vec!["no".to_owned()]
            }
            VarCond::Eq(VoL::Lit(lit)) => {
                vec![lit.to_owned()]
            }
            VarCond::Match(glob) if !glob.contains("*") => glob_enumerate(glob),
            _ => Default::default(),
        },
        Guard::And(v) | Guard::Or(v) => v.iter().map(|g| enumerate_literal(g)).flatten().collect(),
        _ => Default::default(),
    }
}

fn normalize(values: Vec<String>) -> Vec<String> {
    if values.iter().all(|value| value.parse::<usize>().is_ok()) {
        let mut nums: Vec<usize> = values
            .into_iter()
            .map(|value| value.parse::<usize>().unwrap())
            .collect::<HashSet<_>>()
            .into_iter()
            .collect();
        nums.sort();
        nums.into_iter().map(|num| num.to_string()).collect()
    } else {
        let mut literals: Vec<String> = values;
        literals.sort();
        literals
    }
}
