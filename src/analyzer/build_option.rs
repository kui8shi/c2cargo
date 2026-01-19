use bincode::{Decode, Encode};
use std::collections::{HashMap, HashSet};
use std::{
    hash::{DefaultHasher, Hash, Hasher},
    path::PathBuf,
};

use super::{
    guard::{Atom, Guard, VarCond, VoL},
    Analyzer, M4Macro, NodeId,
};
use crate::analyzer::as_single;
use crate::utils::llm_analysis::LLMAnalysis;
use crate::{
    analyzer::build_option::use_llm::BuildOptionLLMAnalysisResult, utils::glob::glob_enumerate,
};
use heck::ToSnakeCase;
use itertools::Itertools;

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
    pub feature_dependencies: HashMap<String, HashSet<String>>,
    pub cargo_features: Option<HashMap<String, Vec<CargoFeature>>>,
}

/// doc
#[derive(Debug, Clone, Default, Encode, Decode)]
pub(crate) struct CargoFeature {
    pub name: String,
    pub original_build_option: String,
    pub value_map: HashMap<String, FeatureState>,
    pub enabled_by_default: Option<bool>,
}

/// doc
#[derive(Debug, Clone, Default, Encode, Decode)]
pub(crate) struct FeatureState(bool);

impl FeatureState {
    pub fn positive() -> Self {
        Self(true)
    }

    pub fn negative() -> Self {
        Self(false)
    }

    pub fn is_negative(&self) -> bool {
        !self.0
    }
}

#[allow(dead_code)]
impl Analyzer {
    pub(crate) fn get_macro_call(&self, name: &str) -> Option<&Vec<(NodeId, M4Macro)>> {
        self.macro_calls.as_ref().unwrap().get(name)
    }

    pub(crate) fn build_option_info(&self) -> &BuildOptionInfo {
        self.build_option_info.as_ref().unwrap()
    }

    /// Analyze basic properties of build options
    /// Calling this will remove nodes related to build option declaration/overwriting.
    pub(crate) fn run_build_option_analysis(&mut self) {
        self.build_option_info.replace(self.extract_build_options());

        // we add information to guards that touch build options.
        self.find_build_option_guards();

        // remove nodes related to disabling build options.
        // since cargo feature's additive nature, disabling build options is impossible.
        self.ignore_nodes_disabling_options();
        self.extract_dependencies_from_nodes_enabling_options();

        // remove nodes directly taking build option value.
        self.expand_or_ignore_option_value_assignments();

        // collect informations for llm analysis
        self.collect_build_option_contexts();
        self.collect_build_option_value_candidates();

        // remove build option declaraton nodes from targets of later analyses
        self.remove_build_option_declarations();
        self.apply_non_empty_property_of_cargo_features();
    }

    /// Analyze various properties of build options using LLMs
    pub(crate) async fn run_extra_build_option_analysis(&mut self) {
        // Check cache first if enabled
        if self.options.use_build_option_cache {
            if let Some(cached_features) = self.load_build_option_cache() {
                println!("Using cached build option analysis results");
                self.record_collector_mut().set_build_option_cache_used();
                self.build_option_info
                    .as_mut()
                    .unwrap()
                    .cargo_features
                    .replace(cached_features);
                self.apply_non_empty_property_of_cargo_features();
                return;
            }
        }

        // conduct llm analysis
        let mut user = use_llm::LLMUser::new();
        let max_retries = 3;
        let results = user
            .run_llm_analysis(
                self.build_option_info()
                    .build_options
                    .values()
                    .map(|b| (b, &b.value_candidates)),
                max_retries,
            )
            .await;

        self.build_option_info
            .as_mut()
            .unwrap()
            .cargo_features
            .replace(Default::default());
        for result in results {
            let output = result.output;
            if output.representatives.iter().sorted().eq(["no", "yes"]) {
                println!("{}: YesNo", output.option_name);
            } else {
                println!("{}: {:?}", output.option_name, output.representatives);
            }
            if let Some(aliases) = &output.aliases {
                println!("{}: Aliases: {:?}", output.option_name, aliases);
            }

            // Generate Cargo features
            let features = self.construct_cargo_features(&output);
            println!("Cargo features for {}: {:?}", output.option_name, features);

            // Get value_candidates from the build option
            let value_candidates = self
                .build_option_info()
                .build_options
                .get(&output.option_name)
                .map(|b| b.value_candidates.clone())
                .unwrap_or_default();

            // Record the build option analysis result
            self.record_collector_mut().add_build_option_record(
                output.option_name.clone(),
                true, // success
                None, // failure_reason
                result.cost,
                result.duration,
                value_candidates,
                features.iter().map(|f| f.name.clone()).collect(),
                result.retry_count,
            );

            self.build_option_info
                .as_mut()
                .unwrap()
                .cargo_features
                .as_mut()
                .unwrap()
                .insert(output.option_name.clone(), features);
        }
        self.apply_non_empty_property_of_cargo_features();

        // Save to cache if enabled
        if self.options.use_build_option_cache {
            let cargo_features = self.build_option_info().cargo_features.as_ref().unwrap();
            self.save_build_option_cache(cargo_features);
        }
    }

    /// doc
    fn extract_build_options(&self) -> BuildOptionInfo {
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
        for (option_name, build_option) in self.build_option_info().build_options.clone() {
            if self.pool.nodes.contains(build_option.decl_id) {
                self.remove_node(build_option.decl_id);
            }
            if build_option.context.is_empty() {
                // remove build options themselves that have no side effects.
                self.build_option_info
                    .as_mut()
                    .unwrap()
                    .build_options
                    .remove(&option_name);
            }
        }
    }

    fn find_build_option_guards(&mut self) {
        let arg_vars = self
            .build_option_info
            .as_ref()
            .unwrap()
            .arg_var_to_option_name
            .keys()
            .map(|s| s.as_str())
            .collect::<HashSet<_>>();
        for (_, block) in self.blocks.iter_mut() {
            block.guards = block
                .guards
                .iter()
                .map(|guard| convert_guard_var_to_arg(guard, &arg_vars))
                .collect();
        }
    }

    /// doc
    fn collect_build_option_contexts(&mut self) {
        let mut build_options = self
            .build_option_info
            .as_mut()
            .unwrap()
            .build_options
            .drain()
            .collect::<HashMap<_, _>>();
        for build_option in build_options.values_mut() {
            build_option.declaration = self.display_node(build_option.decl_id);
            let mut target_var_stack = build_option.vars.clone();
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

        self.build_option_info.as_mut().unwrap().build_options = build_options;
    }

    fn collect_build_option_value_candidates(&mut self) {
        let mut build_options = self
            .build_option_info
            .as_mut()
            .unwrap()
            .build_options
            .drain()
            .collect::<HashMap<_, _>>();
        for build_option in build_options.values_mut() {
            // Treat "yes" and "no" as value candidates by default
            build_option
                .value_candidates
                .extend(["yes".to_owned(), "no".to_owned()]);
            let mut values = HashSet::new();
            for id in self.collect_descendant_nodes_per_node(build_option.decl_id, false, false) {
                for &block_id in &self.get_node(id).unwrap().info.branches {
                    for guard in self.blocks[block_id].guards.iter() {
                        values.extend(enumerate_literal(guard));
                    }
                }
            }
            build_option
                .value_candidates
                .extend(normalize(values.into_iter().collect()));
        }
        self.build_option_info.as_mut().unwrap().build_options = build_options;
    }

    /// Remove nodes where a build option variable is set to "no".
    fn ignore_nodes_disabling_options(&mut self) {
        use crate::analyzer::{as_literal, as_shell, MayM4};
        use autotools_parser::ast::node::ShellCommand;

        let info = self.build_option_info.as_ref().unwrap();
        let mut nodes_to_remove = Vec::new();

        // Find all assignment nodes where a target variable is set to "no"
        for (node_id, node) in self
            .pool
            .nodes
            .iter()
            .filter(|(node_id, _)| !info.decl_ids.contains(node_id))
        {
            if let MayM4::Shell(ShellCommand::Assignment(lhs, rhs)) = &node.cmd.0 {
                // Check if this assignment is for our target variable
                if info.arg_var_to_option_name.contains_key(lhs.as_str()) {
                    // Check if the right-hand side is the literal "no"
                    if let Some(shell_word) = as_single(rhs).and_then(as_shell) {
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

        let info = self.build_option_info.as_ref().unwrap();
        let mut nodes_to_remove = Vec::new();
        let mut dependencies = HashMap::new();

        // Find all assignment nodes where build option variable is set to "yes"
        for (node_id, node) in self
            .pool
            .nodes
            .iter()
            .filter(|(node_id, _)| !info.decl_ids.contains(node_id))
        {
            if let MayM4::Shell(ShellCommand::Assignment(lhs, rhs)) = &node.cmd.0 {
                let arg_var = lhs.as_str();
                // Check if this assignment is for our target variable
                if let Some(option_name) = info.arg_var_to_option_name.get(arg_var) {
                    // Check if the right-hand side is the literal "yes"
                    if let Some(shell_word) = as_single(rhs).and_then(as_shell) {
                        if let Some(literal) = as_literal(shell_word) {
                            if literal == "yes" {
                                nodes_to_remove.push(node_id);
                                // check if the assign node is guarded by other arg vars.
                                if let Some(another_arg_var) =
                                    self.block_of_node(node_id).and_then(|block| {
                                        block
                                            .guards
                                            .iter()
                                            .flat_map(|guard| match guard {
                                                Guard::N(false, Atom::Arg(name, VarCond::True))
                                                    if arg_var != name =>
                                                {
                                                    Some(name.to_owned())
                                                }
                                                _ => None,
                                            })
                                            .next()
                                    })
                                {
                                    if let Some(dependent_option_name) =
                                        info.arg_var_to_option_name.get(&another_arg_var)
                                    {
                                        // record dependency b/w build options
                                        dependencies
                                            .entry(dependent_option_name.to_owned())
                                            .or_insert_with(HashSet::new)
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

        self.build_option_info
            .as_mut()
            .unwrap()
            .feature_dependencies = dependencies;
    }

    /// Expand or ignore build option value in assignments
    fn expand_or_ignore_option_value_assignments(&mut self) {
        use crate::analyzer::MayM4;
        use autotools_parser::ast::node::ShellCommand;

        let mut nodes_to_remove = Vec::new();

        let info = self.build_option_info.as_ref().unwrap();
        let arg_vars = info.arg_var_to_option_name.keys().collect::<Vec<_>>();

        // Find assignment nodes where build option variable's value is directly used
        for (node_id, node) in self
            .pool
            .nodes
            .iter()
            .filter(|(node_id, _)| !info.decl_ids.contains(node_id))
        {
            if let MayM4::Shell(ShellCommand::Assignment(lhs, _)) = &node.cmd.0 {
                if let Some(arg_var) = arg_vars.iter().find_map(|arg_var| {
                    node.info
                        .usages
                        .contains_key(arg_var.as_str())
                        .then_some(arg_var)
                }) {
                    // An argument variable is used
                    let lhs_loc = node
                        .info
                        .definitions
                        .values()
                        .next()
                        .unwrap()
                        .first()
                        .unwrap();
                    if let Some(guard) = self.get_guards(lhs_loc.node_id).last() {
                        // the node has a condition
                        if is_arg_var_guarded(guard, arg_var) {
                            // the condition is related to the argument variable
                            let is_assigned_variable_always_defined = self
                                .get_node(self.get_parent(node_id).unwrap())
                                .unwrap()
                                .info
                                .propagated_definitions
                                .contains_key(lhs.as_str());

                            let is_match_any =
                                matches!(guard, Guard::N(_, Atom::Arg(_, VarCond::MatchAny)));

                            if is_assigned_variable_always_defined && is_match_any {
                                nodes_to_remove.push(node_id);
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

    /// Generate Cargo features from BuildOptionLLMAnalysisResult
    fn construct_cargo_features(&self, result: &BuildOptionLLMAnalysisResult) -> Vec<CargoFeature> {
        let mut features = Vec::new();

        if result.representatives.iter().sorted().eq(["no", "yes"]) {
            // For boolean options, just use the option name as feature
            features.push(CargoFeature {
                name: result.option_name.clone(),
                original_build_option: result.option_name.clone(),
                value_map: HashMap::from_iter(
                    [
                        ("yes".to_owned(), FeatureState::positive()),
                        ("no".to_owned(), FeatureState::negative()),
                    ]
                    .into_iter()
                    .chain(result.aliases.iter().flat_map(|aliases| {
                        aliases.iter().map(|(from, to)| {
                            let state = match to.as_str() {
                                "yes" => FeatureState::positive(),
                                "no" => FeatureState::negative(),
                                _ => unreachable!(),
                            };
                            (from.clone(), state)
                        })
                    })),
                ),
                enabled_by_default: result.enabled_by_default,
            });
        } else {
            // For enum-like options, generate features by prefixing representatives with option_name
            for representative in &result.representatives {
                if representative == "no" {
                    // the disabled state can be representated by turning off all other exclusive features
                    // TODO: however we may have to treat this case more carefully.
                    continue;
                }
                let feature_name = if representative == &result.option_name {
                    result.option_name.clone()
                } else if representative == "yes" {
                    result.option_name.clone()
                } else {
                    format!("{}_{}", result.option_name, representative.to_snake_case())
                };
                let mut value_map = HashMap::from_iter(
                    [(representative.clone(), FeatureState::positive())]
                        .into_iter()
                        .chain(
                            result
                                .aliases
                                .iter()
                                .flat_map(|aliases| {
                                    aliases.iter().map(|(from, to)| {
                                        (to == representative)
                                            .then_some((from.clone(), FeatureState::positive()))
                                    })
                                })
                                .flatten(),
                        ),
                );
                if value_map.contains_key("yes") {
                    value_map.insert("no".into(), FeatureState::negative());
                }
                features.push(CargoFeature {
                    name: feature_name.clone(),
                    original_build_option: result.option_name.clone(),
                    value_map,
                    enabled_by_default: None,
                });
            }
        }

        features
    }

    /// convert some conditions according to the assumption of empty properties of cargo features
    fn apply_non_empty_property_of_cargo_features(&mut self) {
        for (_, block) in self.blocks.iter_mut() {
            let mut converted = Vec::new();
            for guard in block.guards.iter() {
                let info = self.build_option_info.as_ref().unwrap();
                match convert_empty_argument_guards(
                    guard,
                    &info.arg_var_to_option_name,
                    &info.cargo_features,
                ) {
                    Ok(guard) => converted.push(guard),
                    Err(true) => converted.push(Guard::confirmed(Atom::Tautology)),
                    Err(false) => converted.push(Guard::negated(Atom::Tautology)),
                }
            }
            if are_guards_contradictory(&converted) {
                converted = vec![Guard::negated(Atom::Tautology)];
            }
            block.guards = converted;
        }
    }
}

fn is_arg_var_guarded(guard: &Guard, arg_var: &str) -> bool {
    match guard {
        Guard::N(_, atom) => match atom {
            Atom::Arg(arg, _) if arg == arg_var => true,
            _ => false,
        },
        Guard::And(guards) | Guard::Or(guards) => {
            guards.iter().all(|g| is_arg_var_guarded(g, arg_var))
        }
    }
}

fn convert_guard_var_to_arg(guard: &Guard, arg_vars: &HashSet<&str>) -> Guard {
    match guard {
        Guard::N(negated, atom) => match atom {
            Atom::Var(name, cond) if arg_vars.contains(name.as_str()) => {
                Guard::N(*negated, Atom::Arg(name.clone(), cond.clone()))
            }
            _ => guard.clone(),
        },
        Guard::And(v) => Guard::And(
            v.iter()
                .map(|g| convert_guard_var_to_arg(g, arg_vars))
                .collect(),
        ),
        Guard::Or(v) => Guard::Or(
            v.iter()
                .map(|g| convert_guard_var_to_arg(g, arg_vars))
                .collect(),
        ),
    }
}

fn enumerate_literal(guard: &Guard) -> Vec<String> {
    match guard {
        Guard::N(negated, Atom::Var(_, cond) | Atom::Arg(_, cond)) if !negated => match cond {
            VarCond::Eq(VoL::Lit(lit)) => {
                vec![lit.to_owned()]
            }
            VarCond::Match(glob) if !glob.contains("*") => glob_enumerate(glob),
            _ => Default::default(),
        },
        Guard::And(v) | Guard::Or(v) => v.iter().flat_map(enumerate_literal).collect(),
        _ => Default::default(),
    }
}

fn normalize(values: Vec<String>) -> Vec<String> {
    const MAX_NUM: usize = 10;
    if values.iter().all(|value| value.parse::<usize>().is_ok()) {
        let mut nums: Vec<usize> = values
            .into_iter()
            .map(|value| value.parse::<usize>().unwrap())
            .collect::<HashSet<_>>()
            .into_iter()
            .collect();
        nums.sort();
        nums.into_iter()
            .take(MAX_NUM)
            .map(|num| num.to_string())
            .collect()
    } else {
        let mut literals: Vec<String> = values;
        literals.sort();
        literals.into_iter().take(MAX_NUM).collect()
    }
}

fn convert_empty_argument_guards(
    guard: &Guard,
    arg_var_to_option_name: &HashMap<String, String>,
    cargo_features: &Option<HashMap<String, Vec<CargoFeature>>>,
) -> Result<Guard, bool> {
    match guard {
        Guard::N(negated, atom) => match atom {
            Atom::Arg(name, VarCond::Empty)
                if arg_var_to_option_name.contains_key(name.as_str()) =>
            {
                // we found empty guards of arguments
                // basically cargo features does not hold such empty values.
                // we have to convert this guard to either
                // 1. ⊤,
                // 2. ⊥, or
                // 3. default value of the corresponding cargo feature analyzed by the LLM.
                let option_name = arg_var_to_option_name.get(name.as_str()).unwrap();
                if let Some(features) = cargo_features.as_ref().and_then(|m| m.get(option_name)) {
                    if features.len() == 1 {
                        // boolean feature
                        if let Some(enabled_by_default) = features[0].enabled_by_default {
                            // has default value
                            return Err(enabled_by_default ^ *negated);
                        }
                    }
                }
                // the argument variable found to have no valid state anymore.
                // if negated, evaluated to ⊤,
                // else, evaluated to ⊥.
                Err(*negated)
            }
            _ => Ok(guard.clone()),
        },
        Guard::And(v) => {
            let mut converted = Vec::new();
            for g in v {
                match convert_empty_argument_guards(g, arg_var_to_option_name, cargo_features) {
                    Ok(guard) => converted.push(guard),
                    Err(true) => continue,
                    Err(false) => return Err(false),
                }
            }
            if converted.len() == 1 {
                Ok(converted.pop().unwrap())
            } else {
                Ok(Guard::And(converted))
            }
        }
        Guard::Or(v) => {
            let mut converted = Vec::new();
            for g in v {
                match convert_empty_argument_guards(g, arg_var_to_option_name, cargo_features) {
                    Ok(guard) => converted.push(guard),
                    Err(true) => return Err(true),
                    Err(false) => continue,
                }
            }
            if converted.len() == 1 {
                Ok(converted.pop().unwrap())
            } else {
                Ok(Guard::Or(converted))
            }
        }
    }
}

fn are_guards_contradictory(guards: &[Guard]) -> bool {
    let mut record = HashMap::new();
    for guard in guards {
        match guard {
            Guard::N(negated, Atom::Var(name, VarCond::True) | Atom::Arg(name, VarCond::True)) => {
                let new = !negated;
                if let Some(existing) = record.insert(name, new) {
                    if new != existing {
                        return true;
                    }
                }
            }
            Guard::N(
                negated,
                Atom::Var(name, VarCond::False) | Atom::Arg(name, VarCond::False),
            ) => {
                let new = *negated;
                if let Some(existing) = record.insert(name, new) {
                    if new != existing {
                        return true;
                    }
                }
            }
            _ => {
                // for simplicity ignore other guards
            }
        }
    }
    false
}

impl Analyzer {
    /// Load cached build option analysis results
    fn load_build_option_cache(&self) -> Option<HashMap<String, Vec<CargoFeature>>> {
        let cache_path = self.get_build_option_cache_path();
        if let Ok(content) = std::fs::read(&cache_path) {
            let config = bincode::config::standard();
            if let Ok((cached_features, _)) = bincode::decode_from_slice::<
                HashMap<String, Vec<CargoFeature>>,
                _,
            >(&content, config)
            {
                println!("Loaded build option cache from: {:?}", cache_path);
                return Some(cached_features);
            }
        }
        None
    }

    /// Save build option analysis results to cache
    fn save_build_option_cache(&self, cargo_features: &HashMap<String, Vec<CargoFeature>>) {
        let cache_path = self.get_build_option_cache_path();
        let config = bincode::config::standard();
        if let Ok(content) = bincode::encode_to_vec(cargo_features, config) {
            if let Ok(()) = std::fs::write(&cache_path, content) {
                println!("Saved build option cache to: {:?}", cache_path);
            }
        }
    }

    /// Get the cache file path for build options, similar to VSA cache
    fn get_build_option_cache_path(&self) -> PathBuf {
        let mut hasher = DefaultHasher::new();
        self.path.to_str().unwrap().hash(&mut hasher);
        // Hash the build option names and value candidates to ensure cache validity
        if let Some(build_options) = &self.build_option_info {
            for (name, option) in build_options
                .build_options
                .iter()
                .sorted_by_key(|(k, _)| k.as_str())
            {
                name.hash(&mut hasher);
                option.value_candidates.hash(&mut hasher);
                option.declaration.hash(&mut hasher);
            }
        }
        let h = hasher.finish();
        PathBuf::from(format!("/tmp/build_option_cache.{:x}.bin", h))
    }
}
