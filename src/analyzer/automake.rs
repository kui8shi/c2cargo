use std::process::Command;
use std::{
    collections::{HashMap, HashSet},
    path::{Path, PathBuf},
};

use autotools_parser::ast::am::AmIdent;
use autotools_parser::{
    ast::{
        am::{AmAssignOp, AmLine, AmVar, AmWord, AmWordFragment, MakeParameter, MayAm},
        builder::AutomakeNodeBuilder,
        minimal::Word,
        node::{Node, NodeId, WordFragment},
    },
    lexer::Lexer,
    parse::automake::AutomakeParser,
};
use regex::{Captures, Regex};
use slab::Slab;

use crate::utils::enumerate::enumerate_combinations;

use super::Guard;

use super::Analyzer;

type AmNode = Node<AmLine, AmNodeInfo>;

/// Represents a node extension in the dependency graph
#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct AmNodeInfo {
    node_id: NodeId,
    condition: Vec<AmGuard>,
}

#[allow(dead_code)]
#[derive(Debug, Clone, Default)]
pub(super) struct AmTarget {
    name: String,
    // program_SOURCES, EXTRA_program_SOURCES,
    sources: HashSet<WithGuard<PathBuf>>,
    // program_LIBADD, program_LDADD,
    links: HashSet<WithGuard<PathBuf>>,
    // program_DEPENDENCIES, EXTRA_program_DEPENDENCIES,
    dependencies: Vec<WithGuard<AmValue>>,
    // program_LDFLAGS
    ldflags: Option<Vec<AmValue>>,
    // program_AR
    cmd_ar: Option<Vec<AmValue>>,
    // program_LINK
    cmd_link: Option<Vec<AmValue>>,
    // program_CFLAGS
    cflags: Option<Vec<AmValue>>,
    // program_CCASFLAGS
    ccasflags: Option<Vec<AmValue>>,
    // program_CPPFLAGS
    cppflags: Option<Vec<AmValue>>,
    // program_CXXFLAGS
    cxxflags: Option<Vec<AmValue>>,
    // program_SHORTNAME
    shortname: Option<AmValue>,
}

#[allow(dead_code)]
#[derive(Debug, Clone, Default)]
pub(super) struct AutomakeFile {
    pub this_file_path: PathBuf,
    pub include_paths: Vec<PathBuf>,
    pub sub_dir_paths: Vec<PathBuf>,
    pub programs: HashMap<String, Vec<AmTarget>>,
    pub libraries: HashMap<String, Vec<AmTarget>>,
    pub headers: HashMap<String, Vec<WithGuard<String>>>,
    pub data: HashMap<String, Vec<WithGuard<String>>>,
    pub dirs: HashMap<String, WithGuard<AmValue>>,
    pub extra_dist: Vec<String>,
    pub built_sources: Vec<PathBuf>,
    pub raw_variable_info: HashMap<String, Vec<WithGuard<AmWord>>>,
}

#[allow(dead_code)]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(super) struct WithGuard<T> {
    value: T,
    am_cond: Vec<AmGuard>,
}

#[allow(dead_code)]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct AmGuard {
    negated: bool,
    var: String,
}

#[derive(Debug, Clone, Default)]
pub(super) struct AutomakeAnalyzer {
    pub files: HashMap<PathBuf, AutomakeFile>,
    pub am_cond_to_guard: HashMap<String, Guard>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(super) enum AmValue {
    Var(String),
    Lit(String),
    Concat(Vec<Self>),
}

impl Into<AmValue> for &Vec<AmIdent> {
    fn into(self) -> AmValue {
        let v = self
            .into_iter()
            .map(|i| match i {
                AmIdent::Raw(s) => AmValue::Lit(s.into()),
                AmIdent::Template(t) => AmValue::Var(t.into()),
            })
            .collect::<Vec<_>>();
        if v.len() == 1 {
            v.first().unwrap().clone()
        } else {
            AmValue::Concat(v)
        }
    }
}

fn as_single(word: &AmWord) -> Option<&AmWordFragment> {
    if let Word::Single(am_word) = &word.0 {
        Some(am_word)
    } else {
        None
    }
}

fn as_shell(word: &AmWordFragment) -> Option<&WordFragment<AmWord>> {
    if let MayAm::Shell(shell_word) = &word {
        Some(shell_word)
    } else {
        None
    }
}

fn as_literal(word: &WordFragment<AmWord>) -> Option<&str> {
    if let WordFragment::Literal(lit) = &word {
        Some(lit.as_str())
    } else {
        None
    }
}

fn as_am(word: &AmWordFragment) -> Option<&AmVar> {
    if let MayAm::Automake(am) = &word {
        Some(am)
    } else {
        None
    }
}

fn as_am_var(am: &AmVar) -> Option<&Vec<AmIdent>> {
    if let AmVar::Param(MakeParameter::Var(var)) = &am {
        Some(var)
    } else {
        None
    }
}

fn as_template(am: &AmVar) -> Option<&str> {
    if let AmVar::Template(var) = &am {
        Some(var)
    } else {
        None
    }
}

impl Analyzer {
    pub(super) fn automake(&self) -> &AutomakeAnalyzer {
        self.automake.as_ref().unwrap()
    }

    pub(super) fn automake_mut(&mut self) -> &mut AutomakeAnalyzer {
        self.automake.as_mut().unwrap()
    }

    pub(super) fn analyze_automake_files(&mut self) {
        self.automake.replace(Default::default());

        for path in self.project_info.am_files.clone() {
            let automake = self.analyze_automake_file(&path, vec![]);
            self.automake_mut().files.insert(path.into(), automake);
        }
        let files = self.automake().files.keys().cloned().collect::<Vec<_>>();
        self.project_info.am_files.extend(files);
        self.extract_source_files();
        self.extract_header_files();
    }

    fn analyze_automake_file(&mut self, path: &Path, mut condition: Vec<AmGuard>) -> AutomakeFile {
        let path = std::fs::canonicalize(path).expect(&format!("Unable to find {:?}", path));
        let project_dir = self.project_info.project_dir.clone();
        let contents = load_automake_file(&path, &project_dir);
        let lexer = Lexer::new(contents.chars());
        let (nodes, top_ids) =
            AutomakeParser::<_, AutomakeNodeBuilder<AmNodeInfo>>::new(lexer).parse_all();
        let mut nodes = nodes
            .into_iter()
            .map(|(node_id, mut n)| {
                n.info.node_id = node_id;
                (node_id, n)
            })
            .collect::<Slab<AmNode>>();
        let mut vars = HashMap::new();
        let mut automake = AutomakeFile::default();
        automake.this_file_path = path
            .strip_prefix(&self.project_info.project_dir)
            .unwrap()
            .to_owned();
        for id in top_ids.iter() {
            self.analyze_automake_variables(*id, &mut nodes, &mut condition, &mut vars);
            if let Some(AmLine::Include(w)) = nodes.get(*id).map(|n| &n.cmd) {
                // TODO: we rather should expand including contents before parsing
                if let Word::Single(MayAm::Shell(WordFragment::Literal(lit))) = &w.0 {
                    let relative = PathBuf::from(lit);
                    if let Some(include_path) = resolve_path(&relative, &path, &project_dir) {
                        automake.include_paths.push(include_path.clone());
                        if !self.automake().files.contains_key(&include_path) {
                            let node_condition = nodes.get(*id).unwrap().info.condition.clone();
                            let res = self.analyze_automake_file(&include_path, node_condition);
                            self.automake_mut().files.insert(include_path, res);
                        }
                    }
                }
            }
        }

        if let Some(subdir_vals) = vars.get("SUBDIRS") {
            for subdir_val in subdir_vals {
                if let Some(lit) = as_single(&subdir_val.value)
                    .and_then(as_shell)
                    .and_then(as_literal)
                {
                    let relative = PathBuf::from(lit).join("Makefile.am");
                    if let Some(sub_path) = resolve_path(&relative, &path, &project_dir) {
                        automake.sub_dir_paths.push(sub_path.clone());
                        if !self.automake().files.contains_key(&sub_path) {
                            let val_condition = subdir_val.am_cond.clone();
                            let res = self.analyze_automake_file(&sub_path, val_condition);
                            self.automake_mut().files.insert(sub_path, res);
                        }
                    }
                }
            }
        }

        for val in self.resolve_automake_var(&vars, "BUILT_SOURCES") {
            if !val.am_cond.is_empty() {
                continue;
            }
            let src = match val.value {
                AmValue::Lit(lit) => PathBuf::from(lit),
                _ => continue,
            };
            automake.built_sources.push(src);
        }

        for dir in vars.keys().filter_map(|name| name.strip_suffix("dir")) {
            let dir_var = format!("{}dir", dir);
            if let Some(val) = self.resolve_automake_var(&vars, &dir_var).first() {
                automake.dirs.insert(dir.to_owned(), val.clone());
            }
        }

        for dir in vars
            .keys()
            .filter_map(|name| name.strip_suffix("_LTLIBRARIES"))
        {
            let libraries_var = format!("{}_LTLIBRARIES", dir);
            let mut resolved: Vec<WithGuard<String>> = Vec::new();
            for val in self.resolve_automake_var(&vars, &libraries_var) {
                if !val.am_cond.is_empty() {
                    continue;
                }
                resolved.extend(self.resolve_automake_value(&val));
            }
            for val in resolved {
                if !val.am_cond.is_empty() {
                    continue;
                }
                let lib = val.value;
                if !lib.ends_with(".la") {
                    continue;
                }
                let target_name = automake_canonicalize(&lib);
                let target = self.automake_new_target(
                    target_name.as_str(),
                    &vars,
                    automake.this_file_path.parent(),
                    &automake.built_sources,
                );
                automake
                    .libraries
                    .entry(dir.to_owned().into())
                    .or_default()
                    .push(target);
            }
        }

        for dir in vars
            .keys()
            .filter_map(|name| name.strip_suffix("_PROGRAMS"))
        {
            let programs_var = format!("{}_PROGRAMS", dir);
            for val in self.resolve_automake_var(&vars, &programs_var) {
                if !val.am_cond.is_empty() {
                    continue;
                }
                let prog = match val.value {
                    AmValue::Lit(lit) => lit,
                    _ => continue,
                };
                let name = prog.replace(".", "_");
                let target = self.automake_new_target(
                    name.as_str(),
                    &vars,
                    automake.this_file_path.parent(),
                    &automake.built_sources,
                );
                automake
                    .programs
                    .entry(dir.to_owned().into())
                    .or_default()
                    .push(target);
            }
        }
        automake
    }

    fn automake_new_target(
        &self,
        name: &str,
        vars: &HashMap<String, Vec<WithGuard<AmWord>>>,
        base_dir: Option<&Path>,
        built_sources: &[PathBuf],
    ) -> AmTarget {
        let collect_values = |keys: &[String]| {
            let mut values = Vec::new();
            for key in keys {
                if vars.contains_key(key) {
                    values.extend(self.resolve_automake_var(vars, key));
                }
            }
            values
        };
        let collect_words = |keys: &[String]| {
            let v = collect_values(keys)
                .into_iter()
                .map(|am_value| am_value.value)
                .collect::<Vec<_>>();
            (!v.is_empty()).then_some(v)
        };
        let collect_paths = |keys: &[String]| {
            let mut values = HashSet::new();
            for key in keys {
                if vars.contains_key(key) {
                    values.extend(self.resolve_automake_path(vars, key, base_dir, built_sources));
                }
            }
            values
        };
        let mut sources = collect_paths(&[
            format!("{}_SOURCES", name),
            format!("EXTRA_{}_SOURCES", name),
        ]);
        if sources.is_empty() {
            let default_source_file = PathBuf::from(name).with_extension("c");
            let path = match base_dir {
                Some(dir) => dir.join(&default_source_file),
                None => default_source_file.clone(),
            };
            if path.exists() {
                sources.insert(WithGuard {
                    value: path,
                    am_cond: Default::default(),
                });
            }
        }
        let links = collect_paths(&[format!("{}_LIBADD", name), format!("{}_LDADD", name)]);
        let dependencies = collect_values(&[
            format!("{}_DEPENDENCIES", name),
            format!("EXTRA_{}_DEPENDENCIES", name),
        ]);
        let ldflags = collect_words(&[format!("{}_LDFLAGS", name)]);
        let cmd_ar = collect_words(&[format!("{}_AR", name)]);
        let cmd_link = collect_words(&[format!("{}_LINK", name)]);
        let cflags = collect_words(&[format!("{}_CFLAGS", name)]);
        let ccasflags = collect_words(&[format!("{}_CCASFLAGS", name)]);
        let cppflags = collect_words(&[format!("{}_CPPFLAGS", name)]);
        let cxxflags = collect_words(&[format!("{}_CXXFLAGS", name)]);
        let shortname =
            collect_words(&[format!("{}_SHORTNAME", name)]).map(|mut v| v.pop().unwrap());
        AmTarget {
            name: name.to_owned(),
            sources,
            links,
            dependencies,
            ldflags,
            cmd_ar,
            cmd_link,
            cflags,
            ccasflags,
            cppflags,
            cxxflags,
            shortname,
        }
    }

    fn resolve_automake_var<'a>(
        &self,
        vars: &'a HashMap<String, Vec<WithGuard<AmWord>>>,
        var: &'a str,
    ) -> Vec<WithGuard<AmValue>> {
        let resolve_word = |w: &MayAm<_, _>| match w {
            MayAm::Shell(w) => {
                if let Some(lit) = as_literal(w) {
                    HashSet::from([AmValue::Lit(lit.to_owned())])
                } else {
                    Default::default()
                }
            }
            MayAm::Automake(am_var) => match am_var {
                AmVar::Param(MakeParameter::Var(ident)) => {
                    let mut resolved = HashSet::new();
                    for ref var in self.resolve_automake_identifier(ident) {
                        if vars.contains_key(var) {
                            resolved.extend(
                                self.resolve_automake_var(&vars, var)
                                    .into_iter()
                                    .filter_map(|with_guard| {
                                        with_guard.am_cond.is_empty().then_some(with_guard.value)
                                    }),
                            );
                        } else {
                            resolved.insert(AmValue::Var(var.to_owned()));
                        }
                    }
                    resolved
                }
                AmVar::Template(template) => HashSet::from([AmValue::Var(template.to_owned())]),
                _ => Default::default(),
            },
            _ => Default::default(),
        };
        if let Some(vals) = vars.get(var) {
            vals.into_iter()
                .map(|val| {
                    let values = match &val.value.0 {
                        Word::Empty => Vec::new(),
                        Word::Single(word) => resolve_word(word).into_iter().collect(),
                        Word::Concat(words) => {
                            enumerate_combinations(words.iter().map(resolve_word).collect())
                                .into_iter()
                                .map(concat_am_values)
                                .collect()
                        }
                    };
                    values.into_iter().map(|value| WithGuard {
                        value,
                        am_cond: val.am_cond.clone(),
                    })
                })
                .flatten()
                .collect()
        } else {
            vec![WithGuard {
                value: AmValue::Var(var.to_owned()),
                am_cond: Default::default(),
            }]
        }
    }

    fn resolve_automake_value(&self, val: &WithGuard<AmValue>) -> HashSet<WithGuard<String>> {
        match &val.value {
            AmValue::Var(var) => self
                .resolve_var(&var, None, false)
                .into_iter()
                .map(|s| WithGuard {
                    value: s,
                    am_cond: val.am_cond.clone(),
                })
                .collect::<HashSet<_>>(),
            AmValue::Lit(lit) => HashSet::from([WithGuard {
                value: lit.clone(),
                am_cond: val.am_cond.clone(),
            }]),
            AmValue::Concat(values) => enumerate_combinations(
                values
                    .iter()
                    .map(|v| {
                        let with_guard = WithGuard {
                            value: v.clone(),
                            am_cond: val.am_cond.clone(),
                        };
                        self.resolve_automake_value(&with_guard)
                    })
                    .collect(),
            )
            .into_iter()
            .map(|combo| {
                let value = combo
                    .iter()
                    .map(|w| w.value.clone())
                    .collect::<Vec<_>>()
                    .concat();
                let am_cond = if let Some(a) = combo.first() {
                    let first = a.am_cond.clone();
                    first
                        .iter()
                        .enumerate()
                        .take_while(|(i, x)| combo.iter().all(|a| a.am_cond.get(*i) == Some(x)))
                        .map(|(_, x)| x.clone())
                        .collect()
                } else {
                    Vec::new()
                };
                WithGuard { value, am_cond }
            })
            .collect(),
        }
    }

    fn resolve_automake_path<'a>(
        &self,
        vars: &'a HashMap<String, Vec<WithGuard<AmWord>>>,
        var: &'a str,
        base_dir: Option<&Path>,
        built_sources: &[PathBuf],
    ) -> HashSet<WithGuard<PathBuf>> {
        let alternative_extensions = ["c", "cc", "cpp", "asm", "s", "S"];

        // Pre-build a lookup map for dynamic links to avoid linear searches
        let mut dynamic_link_map: HashMap<&PathBuf, &Vec<PathBuf>> = HashMap::new();
        for (from_paths, to_paths) in &self.project_info.dynamic_links {
            for from_path in from_paths {
                dynamic_link_map.insert(from_path, to_paths);
            }
        }

        let find_files = |path: PathBuf| -> HashSet<PathBuf> {
            let mut found = HashSet::new();
            let candidates = std::iter::once(path.clone()).chain(
                alternative_extensions
                    .iter()
                    .map(|ext| path.with_extension(ext)),
            );
            for candidate in candidates {
                let path = match base_dir {
                    Some(dir) => dir.join(&candidate),
                    None => candidate.clone(),
                };
                if path.exists() || built_sources.contains(&candidate) {
                    found.insert(path);
                    break;
                } else if let Some(to_paths) = dynamic_link_map.get(&path) {
                    found.extend((*to_paths).iter().cloned());
                    break;
                }
            }
            found
        };
        let mut result = HashSet::new();
        for val in self.resolve_automake_var(vars, var) {
            match val.value {
                AmValue::Var(var) => {
                    result.extend(
                        self.resolve_var(&var, None, false)
                            .into_iter()
                            .map(|value| PathBuf::from(value))
                            .flat_map(|path| find_files(path))
                            .map(|path| WithGuard {
                                value: path,
                                am_cond: Default::default(),
                            }),
                    );
                }
                AmValue::Lit(lit) => {
                    result.extend(find_files(PathBuf::from(lit)).into_iter().map(|path| {
                        WithGuard {
                            value: path,
                            am_cond: val.am_cond.clone(),
                        }
                    }))
                }
                AmValue::Concat(_) => {}
            }
        }
        result
    }

    fn resolve_automake_identifier(&self, ident: &Vec<AmIdent>) -> Vec<String> {
        enumerate_combinations(
            ident
                .into_iter()
                .map(|i| match i {
                    AmIdent::Raw(n) => HashSet::from([n.clone()]),
                    AmIdent::Template(t) => self.resolve_var(t, None, false),
                })
                .collect(),
        )
        .into_iter()
        .map(|combo| combo.concat())
        .collect()
    }

    fn resolve_automake_word(&self, ident: &AmWord) -> Vec<String> {
        let resolve_word = |w: &MayAm<_, _>| match w {
            MayAm::Shell(w) => {
                if let Some(lit) = as_literal(w) {
                    return HashSet::from([lit.to_owned()]);
                } else {
                    Default::default()
                }
            }
            MayAm::Automake(am_var) => match am_var {
                AmVar::Template(template) => self.resolve_var(&template, None, false),
                // an automake identifier is assumed not to have any make parameters (e.g. $(var)) embedded.
                _ => Default::default(),
            },
            _ => Default::default(),
        };
        match &ident.0 {
            Word::Empty => Vec::new(),
            Word::Single(word) => resolve_word(word).into_iter().collect(),
            Word::Concat(words) => enumerate_combinations(words.iter().map(resolve_word).collect())
                .into_iter()
                .map(|combo| combo.concat())
                .collect(),
        }
    }

    fn analyze_automake_variables(
        &self,
        id: NodeId,
        nodes: &mut Slab<AmNode>,
        conds: &mut Vec<AmGuard>,
        vars: &mut HashMap<String, Vec<WithGuard<AmWord>>>,
    ) {
        nodes.get_mut(id).unwrap().info.condition = conds.clone();
        match nodes.get(id).unwrap().cmd.clone() {
            AmLine::Assignment(assign) => {
                let values = assign
                    .rhs
                    .iter()
                    .map(|w| WithGuard {
                        value: w.clone(),
                        am_cond: conds.clone(),
                    })
                    .collect::<Vec<_>>();
                for name in self.resolve_automake_word(&assign.lhs) {
                    match &assign.op {
                        AmAssignOp::Instant | AmAssignOp::Lazy => {
                            vars.insert(name, values.clone());
                        }
                        AmAssignOp::Append => {
                            vars.entry(name)
                                .or_insert_with(Vec::new)
                                .extend(values.clone());
                        }
                    }
                }
            }
            AmLine::Conditional(conditional) => {
                let var = &conditional.guard_var;
                let negated = conditional.negated;
                conds.push(AmGuard {
                    negated,
                    var: var.clone(),
                });
                for id in conditional.then.iter() {
                    self.analyze_automake_variables(*id, nodes, conds, vars);
                }
                conds.pop();
                conds.push(AmGuard {
                    negated: !negated,
                    var: var.clone(),
                });
                for id in conditional.otherwise.iter() {
                    self.analyze_automake_variables(*id, nodes, conds, vars);
                }
                conds.pop();
            }
            _ => (),
        }
    }

    fn extract_source_files(&mut self) {
        for (_, am_file) in self.automake.as_ref().unwrap().files.iter() {
            for target in am_file
                .libraries
                .get("lib")
                .iter()
                .map(|v| v.iter())
                .flatten()
            {
                self.project_info.c_files.extend(
                    target
                        .sources
                        .iter()
                        .chain(target.links.iter())
                        // .filter(|v| v.am_cond.is_empty()) // FIXME
                        .filter(|v| v.value.extension().is_some_and(|ext| ext == "c"))
                        .filter(|v| !am_file.built_sources.contains(&v.value))
                        .map(|v| v.value.clone()),
                );
            }
            self.project_info.built_files.extend(
                am_file
                    .built_sources
                    .iter()
                    .cloned()
                    .filter(|v| v.extension().is_some_and(|ext| ext == "c")),
            );
        }
    }

    fn extract_header_files(&mut self) {
        for (_, am_file) in self.automake.as_ref().unwrap().files.iter() {
            self.project_info.built_files.extend(
                am_file
                    .built_sources
                    .iter()
                    .cloned()
                    .filter(|v| v.extension().is_some_and(|ext| ext == "h")),
            );
        }
        let will_be_generated = self
            .project_info
            .built_files
            .iter()
            .chain(self.project_info.config_files.iter().map(|(dst, _)| dst))
            .chain(self.project_info.subst_files.iter().map(|(dst, _)| dst))
            .chain(
                self.project_info
                    .dynamic_links
                    .iter()
                    .map(|(from, _)| from.iter())
                    .flatten(),
            )
            .collect::<HashSet<_>>();
        self.project_info.h_files.extend(
            self.project_info
                .c_files
                .iter()
                .map(|c_file| {
                    get_included_headers(c_file, &self.project_info.project_dir).into_iter()
                })
                .flatten()
                .filter(|h| !will_be_generated.contains(&h))
                .collect::<HashSet<_>>(),
        );
    }
}

/// Get a unique set of included headers.
fn get_included_headers(file_path: &Path, base_dir: &Path) -> HashSet<PathBuf> {
    // Execute GCC and capture stdout. -MG allows missing headers.
    let output = Command::new("gcc")
        .args([file_path.to_str().unwrap(), "-MG", "-MM"])
        .current_dir(base_dir)
        .output();

    let Ok(out) = output else {
        return HashSet::new();
    };
    if !out.status.success() {
        return HashSet::new();
    };

    let Ok(stdout_str) = std::str::from_utf8(&out.stdout) else {
        return HashSet::new();
    };

    let mut headers = HashSet::new();

    for line in stdout_str.lines() {
        let clean_line = line.trim_end_matches('\\').trim();

        for part in clean_line.split_whitespace() {
            if !part.contains(':') && part != file_path {
                let header_file = PathBuf::from(part);
                if base_dir.join(&header_file).exists() {
                    headers.insert(header_file);
                } else if let Some(parent) = file_path.parent() {
                    if parent.join(&header_file).exists() {
                        headers.insert(parent.join(&header_file));
                    }
                }
            }
        }
    }

    headers
}

/// Recursively loads Automake files and resolves includes.
fn load_automake_file(path: &Path, project_dir: &Path) -> String {
    let bytes = std::fs::read(path).expect("Reading a file has failed.");
    let contents = String::from_utf8_lossy(&bytes);

    // Remove "$U" artifacts
    let contents = contents.replace("$U", "");

    let contents = {
        // `(?m)` enables multi-line mode so `^` matches the start of each line in the file, not just the first line.
        let include_re = Regex::new(r"(?m)^include\s+(?<file>.+)").unwrap();

        include_re
            .replace_all(&contents, |caps: &Captures| {
                let file = PathBuf::from(caps.name("file").unwrap().as_str());

                // Resolve the full path of the included file
                let include_path =
                    resolve_path(&file, path, &project_dir).expect("Failed at resolving a path.");
                // Recursively load the included file
                let full_read_path = project_dir.join(&include_path);
                load_automake_file(&full_read_path, project_dir)
            })
            .into_owned()
    };

    contents
}

fn resolve_path(relative: &Path, current: &Path, project_dir: &Path) -> Option<PathBuf> {
    let full = if let Some(dir) = current.parent() {
        dir.join(relative)
    } else {
        relative.into()
    };
    match std::fs::canonicalize(full) {
        Err(_) => None,
        Ok(canonical) => {
            if canonical == current {
                None
            } else {
                canonical
                    .strip_prefix(project_dir)
                    .ok()
                    .map(|p| p.to_owned())
            }
        }
    }
}

fn concat_am_values(values: Vec<AmValue>) -> AmValue {
    let mut values = values.into_iter().fold(Vec::new(), |mut acc, e| {
        let merged_value = acc.last().and_then(|last| {
            if let (AmValue::Lit(last), AmValue::Lit(new)) = (last, &e) {
                Some(AmValue::Lit(last.clone() + new))
            } else {
                None
            }
        });
        if let Some(value) = merged_value {
            acc.pop();
            acc.push(value);
        } else {
            acc.push(e);
        }
        acc
    });
    if values.len() == 1 {
        values.pop().unwrap()
    } else {
        AmValue::Concat(values)
    }
}

fn automake_canonicalize(name: &str) -> String {
    name.chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || c == '_' {
                c
            } else {
                '_'
            }
        })
        .collect()
}
