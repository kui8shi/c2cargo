use std::{
    collections::{HashMap, HashSet},
    path::{Path, PathBuf},
};

use regex::{Captures, Regex};

use super::{automake::WithGuard, Analyzer};
use crate::utils::enumerate::enumerate_combinations;

#[derive(Debug, Default)]
pub(crate) struct ProjectInfo {
    pub project_dir: PathBuf,
    pub c_files: Vec<WithGuard<PathBuf>>,
    pub h_files: Vec<PathBuf>,
    pub cflags_var_names: Vec<String>,
    pub ext_h_files: Vec<PathBuf>,
    pub built_files: HashSet<PathBuf>,
    pub generated_files: HashSet<PathBuf>,
    pub config_files: Vec<(PathBuf, PathBuf)>,
    pub subst_files: Vec<(PathBuf, PathBuf)>,
    pub am_files: Vec<PathBuf>,
    pub dynamic_links: Vec<(Vec<PathBuf>, Vec<PathBuf>)>,
    pub source_contents: Option<HashMap<PathBuf, String>>,
    pub template_contents: Option<HashMap<PathBuf, String>>,
}

impl Analyzer {
    pub(crate) fn load_project_files(&mut self) {
        let template_contents = self
            .get_project_template_paths()
            .into_iter()
            .map(|path| (path.to_owned(), load_source(path)))
            .collect::<HashMap<_, _>>();
        self.project_info
            .template_contents
            .replace(template_contents);

        let source_contents = self
            .get_project_source_paths()
            .into_iter()
            .map(|path| (path.to_owned(), load_source(path)))
            .collect::<HashMap<_, _>>();
        self.project_info.source_contents.replace(source_contents);
    }

    pub(crate) fn get_project_source_paths(&self) -> Vec<&Path> {
        self.project_info
            .c_files
            .iter()
            .map(|w| &w.value)
            .chain(self.project_info.h_files.iter())
            .map(|p| p.as_path())
            .collect()
    }

    pub(crate) fn get_project_source_contents(&self) -> Vec<&str> {
        self.project_info
            .source_contents
            .as_ref()
            .unwrap()
            .values()
            .map(|s| s.as_str())
            .collect()
    }

    fn get_project_template_paths(&self) -> HashSet<&Path> {
        self.project_info
            .subst_files
            .iter()
            .map(|(_, src)| src)
            .chain(
                self.project_info
                    .dynamic_links
                    .iter()
                    .flat_map(|(_, to)| to.iter()),
            )
            .map(|p| p.as_path())
            .collect::<HashSet<_>>()
    }

    pub(crate) fn get_project_template_contents(&self) -> Vec<&str> {
        self.project_info
            .template_contents
            .as_ref()
            .unwrap()
            .values()
            .map(|s| s.as_str())
            .collect()
    }
}

impl Analyzer {
    /// Analyze redirected and removed files to determine actually generated files by running configure script
    pub(crate) fn collect_files_generated_by_script(&mut self) {
        let redirected_files = self.collect_redirected_files();
        let removed_files = self.collect_removed_files();

        // built_files = redirected_files - removed_files
        let generated_files: HashSet<PathBuf> = redirected_files
            .difference(&removed_files)
            .cloned()
            .collect();
        self.project_info.generated_files.extend(generated_files);
    }

    /// Collect files that are redirected to (created/written)
    fn collect_redirected_files(&self) -> HashSet<PathBuf> {
        use crate::analyzer::{as_literal, as_shell, MayM4, ShellCommand};
        use autotools_parser::ast::Redirect;

        let mut redirected_files = HashSet::new();

        // Look for redirection patterns: command > file, command >> file
        for (node_id, node) in self.pool.nodes.iter() {
            if let MayM4::Shell(ShellCommand::Redirect(_, redirections)) = &node.cmd.0 {
                for redirect in redirections {
                    let target_word = match redirect {
                        Redirect::Write(_, word) => Some(word),
                        Redirect::Append(_, word) => Some(word),
                        Redirect::Clobber(_, word) => Some(word),
                        _ => None, // Skip other redirect types (Read, DupRead, etc.)
                    };

                    if let Some(word) = target_word {
                        if let Some(literal) = as_shell(word).and_then(as_literal) {
                            if !literal.starts_with("/") {
                                redirected_files.insert(literal.into());
                            }
                        } else {
                            // Try to resolve variables in the redirection target
                            let resolved_paths = self.resolve_word_as_path(word, node_id);
                            redirected_files.extend(resolved_paths);
                        }
                    }
                }
            }
        }

        redirected_files
    }

    /// Collect files that are removed by rm commands
    fn collect_removed_files(&self) -> HashSet<PathBuf> {
        use crate::analyzer::{as_literal, as_shell, MayM4, ShellCommand};

        let mut removed_files = HashSet::new();

        // Iterate over all nodes looking for rm commands
        for (node_id, node) in self.pool.nodes.iter() {
            if let MayM4::Shell(ShellCommand::Cmd(words)) = &node.cmd.0 {
                if let Some(literal) = words.first().and_then(as_shell).and_then(as_literal) {
                    if literal == "rm" {
                        // Process rm arguments
                        for arg_word in words.iter().skip(1) {
                            if let Some(literal) = as_shell(arg_word).and_then(as_literal) {
                                // Skip flags like -f, -rf, etc.
                                if !literal.starts_with('-') {
                                    removed_files
                                        .insert(self.project_info.project_dir.join(literal));
                                }
                            } else {
                                // Try to resolve variables in the argument
                                let resolved_paths = self.resolve_word_as_path(arg_word, node_id);
                                removed_files.extend(resolved_paths);
                            }
                        }
                    }
                }
            }
        }

        removed_files
    }

    /// Resolve variables in autoconf words to get all possible paths
    fn resolve_word_as_path(
        &self,
        ac_word: &super::AcWord,
        node_id: super::NodeId,
    ) -> HashSet<PathBuf> {
        use autotools_parser::ast::minimal::Word;
        use autotools_parser::ast::node::WordFragment;
        use autotools_parser::ast::Parameter;

        let location = Some(self.get_location_of_node_start(node_id));
        let mut result_paths = HashSet::new();

        // Simple approach: handle common cases and use enumerate_combinations for concat
        match &ac_word.0 {
            Word::Empty => {}
            Word::Single(fragment) => {
                match fragment {
                    super::MayM4::Shell(WordFragment::Literal(lit)) => {
                        if !lit.starts_with('-') && !lit.is_empty() {
                            result_paths.insert(lit.into());
                        }
                    }
                    super::MayM4::Shell(WordFragment::Param(Parameter::Var(var_name))) => {
                        let resolved_values = self.resolve_var(var_name, location, false);
                        for resolved_value in resolved_values {
                            if !resolved_value.starts_with('-') && !resolved_value.is_empty() {
                                result_paths.insert(resolved_value.into());
                            }
                        }
                    }
                    super::MayM4::Shell(WordFragment::DoubleQuoted(fragments)) => {
                        // For simple double quoted cases, collect resolved fragments and combine
                        let resolved_fragments: Vec<HashSet<String>> = fragments
                            .iter()
                            .map(|fragment| match fragment {
                                WordFragment::Literal(lit) => {
                                    let mut result = HashSet::new();
                                    result.insert(lit.clone());
                                    result
                                }
                                WordFragment::Param(Parameter::Var(var_name)) => {
                                    self.resolve_var(var_name, location.clone(), false)
                                }
                                _ => HashSet::new(),
                            })
                            .collect();

                        let combinations = enumerate_combinations(resolved_fragments);
                        for combo in combinations {
                            let combined = combo.concat();
                            if !combined.starts_with('-') && !combined.is_empty() {
                                result_paths.insert(combined.into());
                            }
                        }
                    }
                    _ => {} // Skip other complex cases for now
                }
            }
            Word::Concat(fragments) => {
                // For concat words, try to resolve each fragment and combine
                let resolved_fragments: Vec<HashSet<String>> = fragments
                    .iter()
                    .map(|fragment| match fragment {
                        super::MayM4::Shell(WordFragment::Literal(lit)) => {
                            let mut result = HashSet::new();
                            result.insert(lit.clone());
                            result
                        }
                        super::MayM4::Shell(WordFragment::Param(Parameter::Var(var_name))) => {
                            self.resolve_var(var_name, location.clone(), false)
                        }
                        _ => HashSet::new(),
                    })
                    .collect();

                let combinations = enumerate_combinations(resolved_fragments);
                for combo in combinations {
                    let combined = combo.concat();
                    if !combined.starts_with('-') && !combined.is_empty() {
                        result_paths.insert(combined.into());
                    }
                }
            }
        }

        result_paths
    }
}

fn load_source(path: &Path) -> String {
    // Regex explanation:
    // 1. `"(?:[^"\\]|\\.)*"`: Matches string literals (handles escaped quotes).
    //    We match strings first to ensure `//` or `/*` inside them are not treated as comments.
    // 2. `/\*(?s:.*?)\*/`: Matches block comments `/* ... */`.
    // 3. `//.*`: Matches single-line comments.
    let comment_re = Regex::new(r#""(?:[^"\\]|\\.)*"|/\*(?s:.*?)\*/|//.*"#).expect("Invalid regex");

    // Read file
    let bytes = std::fs::read(path).ok().expect("failed to read");

    // Convert to string (lossy)
    // Note: Assuming `merge_line_continuations` is defined elsewhere or not strictly needed for this snippet.
    let content = merge_line_continuations(&String::from_utf8_lossy(&bytes));

    // Replace comments with a single space to avoid concatenating tokens,
    // but return string literals exactly as they are.
    let cleaned = comment_re.replace_all(&content, |caps: &Captures| {
        let match_str = caps.get(0).unwrap().as_str();

        // If it starts with a quote, it's a string literal; preserve it.
        if match_str.starts_with('"') {
            match_str.to_string()
        } else {
            // Otherwise, it's a comment; replace with a space.
            // (e.g., `int/*comment*/x` becomes `int x`)
            " ".to_string()
        }
    });

    cleaned.into_owned()
}

/// Helper: Merges lines ending with backslash ('\') into single logical lines.
fn merge_line_continuations(content: &str) -> String {
    let mut lines = Vec::new();
    let mut buffer = String::new();

    for raw_line in content.lines() {
        let trimmed = raw_line.trim_end();
        if trimmed.ends_with('\\') {
            // Append content without the backslash
            buffer.push_str(&trimmed[..trimmed.len() - 1]);
            buffer.push(' '); // Safety spacer
        } else {
            buffer.push_str(raw_line);
            lines.push(buffer);
            buffer = String::new();
        }
    }

    if !buffer.is_empty() {
        lines.push(buffer);
    }
    lines.join("\n")
}
