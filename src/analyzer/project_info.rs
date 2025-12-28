use std::{
    collections::{HashMap, HashSet},
    path::{Path, PathBuf},
};

use regex::{Captures, Regex};

use super::{automake::WithGuard, Analyzer};

#[derive(Debug, Default)]
pub(crate) struct ProjectInfo {
    pub project_dir: PathBuf,
    pub c_files: Vec<WithGuard<PathBuf>>,
    pub h_files: Vec<PathBuf>,
    pub built_files: Vec<PathBuf>,
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
