use super::{Analyzer, AstVisitor, Guard, Node, NodeId, Parameter, Word, WordFragment};
use slab::Slab;
use std::collections::{HashMap, HashSet};

/// Represents an `eval` invocation that builds dynamic variable references.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EvalMatch {
    /// The assignment word passed to `eval`, e.g. `cclist_chosen="$cclist$abi1"`.
    pub assignment: Word<String>,
    /// The name of the variable being defined (left side of assignment).
    pub var_name: String,
    /// The names of variables referenced dynamically inside the assignment.
    pub ref_names: Vec<String>,
    /// Literal parts extracted from the assignment for structure analysis.
    pub literal_parts: Vec<String>,
}

/// Represents possible r-values (right-hand side values) for a variable
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum VariableValue {
    /// Direct string literal value
    Literal(String),
    /// Value from command substitution (not evaluated)
    CommandSubst(String),
    /// Value from another variable (for chaining)
    Variable(String),
    /// Value from user-defined variable (ignored in analysis)
    UserDefined,
    /// Value from list expansion (special case)
    ListItem(String),
}

/// Represents a special operation in the backward taint analysis
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SpecialOperation {
    /// List expansion: variable ← (list) ← source_var
    ListExpansion(String),
    /// Command substitution: variable ← (cmd) ← command
    CommandExpansion(String),
    /// Eval expansion: variable ← (eval) ← [var1, var2, ...]
    EvalExpansion(Vec<String>),
}

/// Results of backward taint analysis for a variable
#[derive(Debug, Clone)]
pub struct TaintAnalysisResult {
    /// Possible r-values for this variable
    pub values: HashSet<VariableValue>,
    /// Variables that this variable depends on
    pub dependencies: HashSet<String>,
    /// Special operations encountered in the chain
    pub operations: Vec<SpecialOperation>,
}

/// Backward taint analyzer for variable r-value enumeration
#[derive(Debug)]
pub struct BackwardTaintAnalyzer<'a> {
    nodes: &'a Slab<Node>,
    top_ids: &'a [NodeId],
    /// Cache of analysis results to avoid recomputation
    cache: HashMap<String, TaintAnalysisResult>,
    /// Set of variables that are known to be user-defined
    user_defined: HashSet<String>,
    /// Set of variables currently being analyzed (for cycle detection)
    analyzing: HashSet<String>,
}

impl Analyzer {}

impl<'a> BackwardTaintAnalyzer<'a> {
    pub fn new(nodes: &'a Slab<Node>, top_ids: &'a [NodeId]) -> Self {
        Self {
            nodes,
            top_ids,
            cache: HashMap::new(),
            user_defined: HashSet::new(),
            analyzing: HashSet::new(),
        }
    }

    /// Analyze variable to get all possible r-values via backward taint analysis
    pub fn analyze_variable(&mut self, var_name: &str) -> TaintAnalysisResult {
        if let Some(cached) = self.cache.get(var_name) {
            return cached.clone();
        }

        // Check for cycles - if we're already analyzing this variable, return empty result
        if self.analyzing.contains(var_name) {
            return TaintAnalysisResult {
                values: HashSet::new(),
                dependencies: HashSet::new(),
                operations: Vec::new(),
            };
        }

        // Mark this variable as being analyzed
        self.analyzing.insert(var_name.to_string());

        // println!("Analyzing variable: {}", var_name);
        let mut result = TaintAnalysisResult {
            values: HashSet::new(),
            dependencies: HashSet::new(),
            operations: Vec::new(),
        };

        let mut found_definitions = 0;

        // Find all definitions of this variable by walking backwards through nodes
        for &node_id in self.top_ids.iter().rev() {
            if let Some(node) = self.nodes.get(node_id) {
                if let Some(_) = node.defines.get(var_name) {
                    // println!("Found definition in top node {}", node_id);
                    self.analyze_definition(var_name, node_id, &mut result);
                    found_definitions += 1;
                }
            }
        }

        // Also search in all nodes (including nested ones) for variable definitions
        for (node_id, node) in self.nodes.iter() {
            if let Some(_) = node.defines.get(var_name) {
                // println!("Found definition in node {}", node_id);
                self.analyze_definition(var_name, node_id, &mut result);
                found_definitions += 1;
            }
        }

        // println!("Total definitions found for {}: {}", var_name, found_definitions);

        // Remove from analyzing set
        self.analyzing.remove(var_name);

        // Cache the result
        self.cache.insert(var_name.to_string(), result.clone());
        result
    }

    /// Analyze a specific definition of a variable
    fn analyze_definition(
        &mut self,
        var_name: &str,
        node_id: NodeId,
        result: &mut TaintAnalysisResult,
    ) {
        if let Some(node) = self.nodes.get(node_id) {
            // println!("Analyzing definition of {} in node {} with kind: {:?}", var_name, node_id, node.kind);
            match &node.kind {
                super::NodeKind::Assignment(name, word) if name == var_name => {
                    // println!("Found assignment: {} = {:?}", name, word);
                    self.analyze_assignment_word(word, result);
                }
                super::NodeKind::For { var, words, .. } if var == var_name => {
                    // println!("Found for loop defining {}", var);
                    // Handle for loop variable assignments - extract items from list
                    result
                        .operations
                        .push(SpecialOperation::ListExpansion(var.clone()));
                    for word in words {
                        // For list expansion, we need to get the variable being expanded
                        if let Word::Single(WordFragment::Param(Parameter::Var(list_var))) = word {
                            // Get the values from the list variable
                            let list_analysis = self.analyze_variable(list_var);
                            for value in &list_analysis.values {
                                match value {
                                    VariableValue::Literal(lit) => {
                                        // Split literal by whitespace to get list items
                                        for item in lit.split_whitespace() {
                                            result
                                                .values
                                                .insert(VariableValue::ListItem(item.to_string()));
                                        }
                                    }
                                    _ => {
                                        result.values.insert(value.clone());
                                    }
                                }
                            }
                            result.dependencies.insert(list_var.clone());
                        } else {
                            self.analyze_assignment_word(word, result);
                        }
                    }
                }
                super::NodeKind::For { var, words, body } => {
                    // println!(
                    //     "Checking for loop body for {} definition (loop var: {})",
                    //     var_name, var
                    // );
                    // Search the for loop body for our variable definition (recursively)
                    self.search_nested_definitions(var_name, body, result);
                }
                super::NodeKind::Cmd(cmd_words) => {
                    // Check if this is an eval command defining our variable
                    if self.is_eval_command(cmd_words) {
                        self.analyze_eval_command(var_name, cmd_words, result);
                    }
                }
                _ => {}
            }
        }
    }

    /// Analyze a word in an assignment to extract values
    fn analyze_assignment_word(&mut self, word: &Word<String>, result: &mut TaintAnalysisResult) {
        match word {
            Word::Single(fragment) => {
                self.analyze_word_fragment(fragment, result);
            }
            Word::Concat(fragments) => {
                for fragment in fragments {
                    self.analyze_word_fragment(fragment, result);
                }
            }
            Word::Empty => {}
        }
    }

    /// Analyze a word fragment to extract values and dependencies
    fn analyze_word_fragment(
        &mut self,
        fragment: &WordFragment<String>,
        result: &mut TaintAnalysisResult,
    ) {
        match fragment {
            WordFragment::Literal(lit) => {
                if !lit.is_empty() {
                    result.values.insert(VariableValue::Literal(lit.clone()));
                }
            }
            WordFragment::Param(Parameter::Var(var_name)) => {
                result.dependencies.insert(var_name.clone());
                // Recursively analyze the referenced variable
                let sub_result = self.analyze_variable(var_name);
                result.values.extend(sub_result.values);
                result.dependencies.extend(sub_result.dependencies);
                result.operations.extend(sub_result.operations);

                // Also add the variable itself as a potential value for chaining
                result
                    .values
                    .insert(VariableValue::Variable(var_name.clone()));
            }
            WordFragment::DoubleQuoted(inner_fragments) => {
                for inner_fragment in inner_fragments {
                    self.analyze_word_fragment(inner_fragment, result);
                }
            }
            WordFragment::Subst(subst) => {
                match subst.as_ref() {
                    super::ParameterSubstitution::Command(cmds) => {
                        // Command substitution - for patterns like $(echo _${abi} | sed s/[.]//g)
                        // Try to infer the result pattern
                        let cmd_str = format!("command_substitution_{}", cmds.len());
                        result
                            .operations
                            .push(SpecialOperation::CommandExpansion(cmd_str.clone()));
                        result.values.insert(VariableValue::CommandSubst(cmd_str));

                        // For the common pattern of echo _${var} | sed, try to extract transformation
                        // This is a simplified heuristic for the abi1 case
                        if cmds.len() >= 1 {
                            // Try to simulate common transformations like echo _${abi} | sed s/[.]//g
                            // This would transform abi values to _abi format with dots removed
                            self.simulate_command_transformation(cmds, result);
                        }
                    }
                    _ => {
                        // Other parameter substitutions - could be analyzed further
                    }
                }
            }
            _ => {}
        }
    }

    /// Check if a command is an eval command
    fn is_eval_command(&self, cmd_words: &[Word<String>]) -> bool {
        if let Some(first) = cmd_words.get(0) {
            match first {
                Word::Single(WordFragment::Literal(t)) => t == "eval",
                Word::Concat(frags) => {
                    frags.len() == 1 && matches!(&frags[0], WordFragment::Literal(t) if t == "eval")
                }
                _ => false,
            }
        } else {
            false
        }
    }

    /// Analyze an eval command to extract variable definitions
    fn analyze_eval_command(
        &mut self,
        var_name: &str,
        cmd_words: &[Word<String>],
        result: &mut TaintAnalysisResult,
    ) {
        for assign in &cmd_words[1..] {
            if let Word::Concat(frags) = assign {
                if let Some(WordFragment::Literal(left)) = frags.first() {
                    if let Some(eval_var_name) = left.strip_suffix('=') {
                        if eval_var_name == var_name {
                            // This eval defines our variable
                            let mut eval_vars = Vec::new();

                            // Extract the variables used in the eval expression
                            for frag in frags.iter().skip(1) {
                                self.extract_eval_variables(frag, &mut eval_vars);
                            }

                            if !eval_vars.is_empty() {
                                result
                                    .operations
                                    .push(SpecialOperation::EvalExpansion(eval_vars.clone()));
                                result.dependencies.extend(eval_vars.iter().cloned());
                            }
                        }
                    }
                }
            }
        }
    }

    /// Extract variables used in eval expressions
    fn extract_eval_variables(&mut self, fragment: &WordFragment<String>, vars: &mut Vec<String>) {
        match fragment {
            WordFragment::Param(Parameter::Var(var_name)) => {
                vars.push(var_name.clone());
            }
            WordFragment::DoubleQuoted(inner) => {
                for inner_frag in inner {
                    self.extract_eval_variables(inner_frag, vars);
                }
            }
            _ => {}
        }
    }

    /// Apply collected r-values to evaluate an eval expression
    pub fn evaluate_eval_expression(
        &mut self,
        eval_vars: &[String],
        literal_parts: &[String],
    ) -> Vec<String> {
        // println!("Evaluating eval expression with vars: {:?} and literals: {:?}", eval_vars, literal_parts);
        let mut var_values: Vec<Vec<String>> = Vec::new();

        // Get all possible values for each variable
        for var_name in eval_vars {
            let analysis_result = self.analyze_variable(var_name);
            // println!("Analysis result for {}: {:?}", var_name, analysis_result.values);
            let mut values = Vec::new();

            for value in &analysis_result.values {
                match value {
                    VariableValue::Literal(lit) => values.push(lit.clone()),
                    VariableValue::ListItem(item) => values.push(item.clone()),
                    VariableValue::Variable(var) => {
                        // Chain through to the referenced variable
                        let chained_result = self.analyze_variable(var);
                        for chained_value in &chained_result.values {
                            if let VariableValue::Literal(lit) = chained_value {
                                values.push(lit.clone());
                            } else if let VariableValue::ListItem(item) = chained_value {
                                values.push(item.clone());
                            }
                        }
                    }
                    VariableValue::CommandSubst(cmd_desc) => {
                        // For command substitutions, we cannot safely execute them
                        // Instead, we'll treat them as placeholders or skip them
                        // In a real implementation, this would require more sophisticated analysis
                        // or symbolic execution
                        values.push(format!("[CMD:{}]", cmd_desc));
                    }
                    _ => {} // Skip user-defined for now
                }
            }

            if values.is_empty() {
                // If no values found, might be user-defined, but let's add the variable name as placeholder
                values.push(format!("${{{}}}", var_name));
            }

            var_values.push(values);
        }

        // Generate all combinations of variable values with literal parts
        let combinations = self.generate_combinations(&var_values, literal_parts);

        // Filter out combinations that still contain unresolved variables (placeholders)
        combinations
            .into_iter()
            .filter(|combo| !combo.contains("${"))
            .collect()
    }

    /// Generate all combinations of variable values
    fn generate_combinations(
        &self,
        var_values: &[Vec<String>],
        literal_parts: &[String],
    ) -> Vec<String> {
        if var_values.is_empty() {
            return literal_parts.to_vec();
        }

        let mut results = Vec::new();
        self.generate_combinations_recursive(
            var_values,
            literal_parts,
            &mut Vec::new(),
            0,
            &mut results,
        );
        results
    }

    fn generate_combinations_recursive(
        &self,
        var_values: &[Vec<String>],
        literal_parts: &[String],
        current: &mut Vec<String>,
        index: usize,
        results: &mut Vec<String>,
    ) {
        if index >= var_values.len() {
            // Simply concatenate all variables - literal parts are often suffix/prefix
            let mut result = String::new();
            for val in current.iter() {
                result.push_str(val);
            }
            // Add all literal parts at the end (common pattern for suffixes like "_cflags")
            for lit in literal_parts {
                result.push_str(lit);
            }
            results.push(result);
            return;
        }

        for value in &var_values[index] {
            current.push(value.clone());
            self.generate_combinations_recursive(
                var_values,
                literal_parts,
                current,
                index + 1,
                results,
            );
            current.pop();
        }
    }

    /// Recursively search for variable definitions in nested node structures
    fn search_nested_definitions(
        &mut self,
        var_name: &str,
        node_ids: &[NodeId],
        result: &mut TaintAnalysisResult,
    ) {
        for &node_id in node_ids {
            if let Some(node) = self.nodes.get(node_id) {
                // println!("Recursively checking node {} for {} - defines: {:?}",
                //          node_id, var_name, node.defines.keys().collect::<Vec<_>>());

                // Check if this node defines our variable
                if node.defines.contains_key(var_name) {
                    // println!("Found {} definition in nested node {}", var_name, node_id);
                    self.analyze_definition(var_name, node_id, result);
                }

                // Also check for assignment nodes directly (in case tracking missed them)
                if let super::NodeKind::Assignment(name, word) = &node.kind {
                    if name == var_name {
                        // println!("Found direct assignment {} = {:?} in node {}", name, word, node_id);
                        self.analyze_assignment_word(word, result);
                    }
                }

                // Recursively search in child structures
                match &node.kind {
                    super::NodeKind::If {
                        conditionals,
                        else_branch,
                    } => {
                        for pair in conditionals {
                            self.search_nested_definitions(var_name, &pair.body, result);
                        }
                        self.search_nested_definitions(var_name, else_branch, result);
                    }
                    super::NodeKind::For { body, .. } => {
                        self.search_nested_definitions(var_name, body, result);
                    }
                    super::NodeKind::While(pair) | super::NodeKind::Until(pair) => {
                        self.search_nested_definitions(var_name, &pair.body, result);
                    }
                    super::NodeKind::Brace(body) => {
                        self.search_nested_definitions(var_name, body, result);
                    }
                    super::NodeKind::Subshell(body) => {
                        self.search_nested_definitions(var_name, body, result);
                    }
                    _ => {}
                }
            }
        }
    }

    /// Simulate common command transformations for better analysis
    /// NOTE: This is a simplified heuristic and cannot handle arbitrary shell commands
    fn simulate_command_transformation(
        &mut self,
        cmds: &[super::NodeId],
        result: &mut TaintAnalysisResult,
    ) {
        // This is a placeholder for command transformation analysis
        // In practice, accurately simulating arbitrary shell commands requires:
        // 1. Full shell interpreter or symbolic execution
        // 2. External tool dependencies (sed, awk, etc.)
        // 3. Environment-specific behavior

        // For now, we just mark that a command transformation occurred
        // without trying to guess the output
        result.values.insert(VariableValue::CommandSubst(format!(
            "transformation_of_{}_commands",
            cmds.len()
        )));
    }
}

/// Visitor to find `eval` commands generating dynamic variable references.
#[derive(Debug)]
pub struct EvalAssignmentFinder<'a> {
    nodes: &'a Slab<Node>,
    cursor: Option<NodeId>,
    /// Collected matches of dynamic eval assignments.
    pub matches: Vec<EvalAssignment>,
}

impl<'a> EvalAssignmentFinder<'a> {
    /// Create a new EvalFinder.
    pub fn find_eval(nodes: &'a Slab<Node>, top_ids: &[NodeId]) -> Self {
        let mut s = Self {
            nodes,
            cursor: None,
            matches: Vec::new(),
        };
        for &id in top_ids {
            s.visit_top(id);
        }
        s
    }
}

impl<'a> AstVisitor for EvalAssignmentFinder<'a> {
    fn get_node(&self, node_id: NodeId) -> &Node {
        &self.nodes[node_id]
    }

    fn visit_top(&mut self, node_id: NodeId) {
        let saved = self.cursor.replace(node_id);
        self.walk_node(node_id);
        self.cursor = saved;
    }

    fn visit_node(&mut self, node_id: NodeId) {
        let saved = self.cursor.replace(node_id);
        if !self.get_node(node_id).is_top_node() {
            self.walk_node(node_id);
        }
        self.cursor = saved;
    }

    fn visit_command(&mut self, cmd_words: &[Word<String>]) {
        if let Some(first) = cmd_words.get(0) {
            let is_eval = match first {
                Word::Single(f) => matches!(f, WordFragment::Literal(t) if t == "eval"),
                Word::Concat(frags) => {
                    frags.len() == 1 && matches!(&frags[0], WordFragment::Literal(t) if t == "eval")
                }
                _ => false,
            };
            if is_eval {
                if let Some(Word::Concat(frags)) = cmd_words.get(1) {
                    let mut ea = parse_eval_assignment(frags);
                    ea.node_id = self.cursor.unwrap();
                    self.matches.push(ea)
                }
            }
        }
        self.walk_command(cmd_words);
    }
}

#[derive(Debug, PartialEq, PartialOrd, Eq, Ord)]
pub enum EvalFragment {
    /// String literal. It could be used in lhs or rhs.
    Lit(String),
    /// Variable referenece. It could used in lhs or rhs.
    Var(String),
    /// Dynamically constructed variable name
    /// e.g. \"\$${var1}_${var2}_suffix\" becomes Dyn([Var(var1), Lit(_), Var(var2), Lit(_suffix)])
    Dyn(Vec<EvalFragment>),
}

impl EvalFragment {
    fn used_vars(&self) -> Option<Vec<&str>> {
        use EvalFragment::*;
        match self {
            Lit(_) => None,
            Var(s) => Some(vec![s.as_str()]),
            Dyn(v) => Some(
                v.iter()
                    .map(|e| e.used_vars())
                    .flatten()
                    .flatten()
                    .collect(),
            ),
        }
    }
}

#[derive(Debug, PartialEq, PartialOrd, Eq, Ord)]
pub struct EvalAssignment {
    /// left hand side of eval statement
    pub lhs: EvalFragment,
    /// right hand side of eval statement
    pub rhs: Vec<EvalFragment>,
    /// the node id of this statement
    pub node_id: NodeId,
}

impl EvalAssignment {
    pub fn used_vars(&self) -> Vec<&str> {
        self.rhs
            .iter()
            .filter_map(|e| e.used_vars())
            .flatten()
            .collect()
    }
}

/// parse a body of eval assignment. It is expected to take `word` as a concatenated word fragments
/// currently we don't support mixed lhs value (eigther single literal or single variable)
fn parse_eval_assignment(frags: &[WordFragment<String>]) -> EvalAssignment {
    use EvalFragment::*;
    let mut lhs = None;
    let mut rhs = Vec::new();
    let mut is_lhs = true;
    let mut is_dyn = false;
    for frag in frags.iter() {
        match frag {
            WordFragment::Escaped(s) if s == r#"\""# => {}
            WordFragment::Escaped(s) if s == "$" => {
                is_dyn = true;
            }
            WordFragment::Param(Parameter::Var(s)) if is_lhs => {
                lhs = Some(Var(s.to_owned()));
                is_lhs = false;
            }
            WordFragment::Param(Parameter::Var(s)) if !is_lhs => {
                rhs.push(Var(s.to_owned()));
            }
            WordFragment::Literal(s) if is_lhs => {
                lhs = Some(Lit(s.strip_suffix("=").unwrap().to_owned()));
                is_lhs = false;
            }
            WordFragment::Literal(s) if !is_lhs => {
                rhs.push(Lit(s.strip_prefix("=").unwrap_or(s).to_owned()));
            }
            _ => (),
        }
    }
    if is_dyn {
        rhs = vec![Dyn(rhs)];
    }
    EvalAssignment {
        lhs: lhs.unwrap(),
        rhs,
        node_id: 0, // lazy initialization
    }
}
