use std::collections::{HashMap, HashSet};

use super::{
    guard::{Atom, Guard, VarCond, VoL},
    Analyzer, M4Macro, NodeId,
};
use crate::utils::glob::glob_enumerate;
use crate::utils::llm_analysis::LLMAnalysis;
use heck::ToSnakeCase;

mod use_llm;

/// doc
#[derive(Debug, Clone)]
pub(crate) struct BuildOption {
    decl_id: NodeId,
    option_name: String,
    vars: Vec<String>,
    value_candidates: Vec<String>,
    declaration: String,
    context: Vec<String>,
}

/// doc
#[derive(Debug, Clone, Default)]
pub(crate) struct BuildOptionInfo {
    pub build_options: HashMap<String, BuildOption>,
    pub decl_ids: Vec<NodeId>,
    pub arg_var_to_option_name: HashMap<String, String>,
    pub dependencies: HashMap<String, HashSet<String>>,
}

#[allow(dead_code)]
impl Analyzer {
    pub(crate) fn get_macro_call(&self, name: &str) -> Option<&Vec<(NodeId, M4Macro)>> {
        self.macro_calls.as_ref().unwrap().get(name)
    }

    /// Analyze basic properties of build options
    /// Calling this will remove nodes related to build option declaration/overwriting.
    pub(crate) fn run_build_option_analysis(&mut self) {
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

        // remove build option declaraton nodes from targets of later analyses
        self.remove_build_option_declarations();
    }

    /// Analyze various properties of build options using LLMs
    pub(crate) async fn run_extra_build_option_analysis(&self) {
        // conduct llm analysis
        let mut user = use_llm::LLMUser::new();
        let results = user
            .run_llm_analysis(self.build_option_info.build_options.values().map(|i| (i, &i.value_candidates)))
            .await;

        for res in results {
            let _build_option = self
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
            if let Some(v) = self.get_macro_call(target_macro_name) {
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
                    .filter(|name| !matches!(name.as_str(), "withval" | "enableval"))
                    .cloned()
                    .collect::<Vec<_>>();
                let build_option = BuildOption {
                    decl_id: *node_id,
                    option_name: option_name.clone(),
                    vars: vars.clone(),
                    value_candidates: Vec::new(),
                    declaration: String::new(),
                    context: Vec::new(),
                };
                ret.build_options.insert(option_name.clone(), build_option);
                for id in self.collect_descendant_nodes_per_node(*node_id, false, true) {
                    if !ret.decl_ids.contains(&id) {
                        ret.decl_ids.push(id);
                    }
                }
                ret.arg_var_to_option_name
                    .extend(vars.into_iter().zip(std::iter::repeat(option_name.clone())));
            }
        }
        ret
    }

    fn remove_build_option_declarations(&mut self) {
        for (option_name, build_option) in self.build_option_info.build_options.clone() {
            if self.pool.nodes.contains(build_option.decl_id) {
                self.remove_node(build_option.decl_id);
            }
            if build_option.context.is_empty() {
                // remove build options themselves that have no side effects.
                self.build_option_info.build_options.remove(&option_name);
            }
        }
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
        for build_option in build_options.values_mut() {
            build_option.declaration = self.display_node(build_option.decl_id);
            let mut target_var_stack = Vec::from(build_option.vars.clone());
            let mut visited = HashSet::new();
            while let Some(var) = target_var_stack.pop() {
                if !visited.contains(&var) {
                    visited.insert(var.clone());
                    for id in self.parent_nodes_of_blocks_guarded_by_variable(var.as_str()) {
                        let (defines, _) = self.collect_variables(id);
                        target_var_stack.extend(
                            defines
                                .keys()
                                .filter(|name| {
                                    // heuristics to relate defined variables and target build option
                                    name.to_lowercase()
                                        .contains(build_option.option_name.to_lowercase().as_str())
                                })
                                .cloned(),
                        );
                        build_option.context.push(self.display_node(id));
                    }
                }
            }
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
            for id in self.collect_descendant_nodes_per_node(build_option.decl_id, false, false) {
                for &block_id in &self.get_node(id).unwrap().info.branches {
                    for guard in self.blocks[block_id].guards.iter() {
                        values.extend(enumerate_literal(guard));
                    }
                }
            }
            build_option.value_candidates = normalize(values.into_iter().collect());
        }
        self.build_option_info.build_options = build_options;
    }

    /// Remove nodes where a build option variable is set to "no".
    fn ignore_nodes_disabling_options(&mut self) {
        use crate::analyzer::{as_literal, as_shell, MayM4};
        use autotools_parser::ast::node::ShellCommand;

        let mut nodes_to_remove = Vec::new();

        // Find all assignment nodes where a target variable is set to "no"
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

    /// Remove nodes where build option variable is set to "yes".
    fn extract_dependencies_from_nodes_enabling_options(&mut self) {
        use crate::analyzer::{as_literal, as_shell, MayM4};
        use autotools_parser::ast::node::ShellCommand;

        let mut nodes_to_remove = Vec::new();

        // Find all assignment nodes where build option variable is set to "yes"
        for (node_id, node) in self
            .pool
            .nodes
            .iter()
            .filter(|(node_id, _)| !self.build_option_info.decl_ids.contains(node_id))
        {
            if let MayM4::Shell(ShellCommand::Assignment(lhs, rhs)) = &node.cmd.0 {
                let arg_var = lhs.as_str();
                // Check if this assignment is for our target variable
                if let Some(option_name) =
                    self.build_option_info.arg_var_to_option_name.get(arg_var)
                {
                    // Check if the right-hand side is the literal "yes"
                    if let Some(shell_word) = as_shell(rhs) {
                        if let Some(literal) = as_literal(shell_word) {
                            if literal == "yes" {
                                nodes_to_remove.push(node_id);
                                // check if the assign node is guarded by other arg vars.
                                if let Some(another_arg_var) =
                                    self.block_of_node(node_id)
                                        .map(|block| {
                                            block
                                                .guards
                                                .iter()
                                                .flat_map(|guard| match guard {
                                                    Guard::N(
                                                        false,
                                                        Atom::Arg(name, VarCond::Yes),
                                                    ) if arg_var != name => Some(name.to_owned()),
                                                    _ => None,
                                                })
                                                .next()
                                        })
                                        .flatten()
                                {
                                    if let Some(dependent_option_name) = self
                                        .build_option_info
                                        .arg_var_to_option_name
                                        .get(&another_arg_var)
                                    {
                                        // record dependency b/w build options
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

        // Remove the identified nodes
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
