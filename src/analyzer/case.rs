use super::{AstVisitor, TopLevelCommand, TopLevelWord};
use autoconf_parser::ast::{
    minimal::{CompoundCommand, Word, WordFragment},
    Parameter, PatternBodyPair,
};

/// Represents a matched case statement on a specific variable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CaseMatch {
    /// The variable being matched (the word in `case $var in`).
    pub var: TopLevelWord,
    /// The arms (patterns and bodies) of the case statement.
    pub arms: Vec<PatternBodyPair<TopLevelWord, TopLevelCommand>>,
}

/// Visitor to find case statements matching given variables.
#[derive(Debug)]
pub(super) struct CaseAnalyzer {
    var_names: Vec<String>,
    /// Collected case matches where the variable matches one of `var_names`.
    pub matches: Vec<CaseMatch>,
    pub ids: Vec<usize>,
}

impl CaseAnalyzer {
    /// Create a new MatchFinder for the given variable names.
    pub fn new(var_names: Vec<String>) -> Self {
        Self {
            var_names,
            matches: Vec::new(),
            ids: Vec::new(),
        }
    }
}

impl AstVisitor for CaseAnalyzer {
    fn visit_compound(&mut self, compound: &CompoundCommand<TopLevelWord, TopLevelCommand>) {
        if let CompoundCommand::Case { word, arms } = compound {
            if let Word::Single(fragment) = word {
                if let WordFragment::Param(Parameter::Var(name)) = fragment {
                    if self.var_names.contains(name) {
                        self.matches.push(CaseMatch {
                            var: word.clone(),
                            arms: arms.clone(),
                        });
                    }
                }
            }
        }
        self.walk_compound(compound);
    }
}
