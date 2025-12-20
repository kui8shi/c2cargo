use std::{
    collections::{HashMap, HashSet},
    path::{Path, PathBuf},
};

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
    sources: HashSet<AmValue<PathBuf>>,
    // program_LIBADD, program_LDADD,
    links: HashSet<AmValue<PathBuf>>,
    // program_DEPENDENCIES, EXTRA_program_DEPENDENCIES,
    dependencies: Vec<AmValue<AmVoL>>,
    // program_LDFLAGS
    ldflags: Option<Vec<AmVoL>>,
    // program_AR
    cmd_ar: Option<Vec<AmVoL>>,
    // program_LINK
    cmd_link: Option<Vec<AmVoL>>,
    // program_CFLAGS
    cflags: Option<Vec<AmVoL>>,
    // program_CCASFLAGS
    ccasflags: Option<Vec<AmVoL>>,
    // program_CPPFLAGS
    cppflags: Option<Vec<AmVoL>>,
    // program_CXXFLAGS
    cxxflags: Option<Vec<AmVoL>>,
    // program_SHORTNAME
    shortname: Option<AmVoL>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(super) struct InstallingDirectory(String);

impl From<String> for InstallingDirectory {
    fn from(value: String) -> Self {
        Self(value)
    }
}

#[allow(dead_code)]
#[derive(Debug, Clone, Default)]
pub(super) struct AutomakeFile {
    pub this_file_path: PathBuf,
    pub include_paths: Vec<PathBuf>,
    pub sub_dir_paths: Vec<PathBuf>,
    pub programs: HashMap<InstallingDirectory, Vec<AmTarget>>,
    pub libraries: HashMap<InstallingDirectory, Vec<AmTarget>>,
    pub headers: HashMap<InstallingDirectory, Vec<AmValue<String>>>,
    pub data: HashMap<InstallingDirectory, Vec<AmValue<String>>>,
    pub dirs: HashMap<String, AmValue<AmVoL>>,
    pub extra_dist: Vec<String>,
    pub built_sources: Vec<PathBuf>,
    pub raw_variable_info: HashMap<String, Vec<AmValue<AmWord>>>,
}

#[allow(dead_code)]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(super) struct AmValue<T> {
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum AmVoL {
    Var(String),
    Lit(String),
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

fn as_am(word: &AmWord) -> Option<&AmVar> {
    if let Word::Single(MayAm::Automake(am)) = &word.0 {
        Some(am)
    } else {
        None
    }
}

fn as_am_var(am: &AmVar) -> Option<&str> {
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
        self.extract_source_and_header_files();
    }

    fn analyze_automake_file(&mut self, path: &Path, mut condition: Vec<AmGuard>) -> AutomakeFile {
        dbg!(&path);
        let path = std::fs::canonicalize(path).expect(&format!("Unable to find {:?}", path));
        let project_dir = self.project_info.project_dir.clone();
        let resolve_path = |relative: &Path| {
            let full = if let Some(dir) = path.parent() {
                dir.join(relative)
            } else {
                relative.into()
            };
            match std::fs::canonicalize(full) {
                Err(_) => None,
                Ok(canonical) => {
                    if canonical == path {
                        None
                    } else {
                        canonical
                            .strip_prefix(&project_dir)
                            .ok()
                            .map(|p| p.to_owned())
                    }
                }
            }
        };
        let contents = self.read_automake_file(&path);
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
                    if let Some(include_path) = resolve_path(&relative) {
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
                    if let Some(sub_path) = resolve_path(&relative) {
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
                AmVoL::Var(_) => continue,
                AmVoL::Lit(lit) => PathBuf::from(lit),
            };
            automake.built_sources.push(src);
        }

        for dir in vars.keys().filter_map(|name| name.strip_suffix("dir")) {
            let dir_var = format!("{}_LTLIBRARIES", dir);
            if let Some(val) = self.resolve_automake_var(&vars, &dir_var).first() {
                automake.dirs.insert(dir.to_owned(), val.clone());
            }
        }

        for dir in vars
            .keys()
            .filter_map(|name| name.strip_suffix("_LIBRARIES"))
        {
            let libraries_var = format!("{}_LTLIBRARIES", dir);
            for val in self.resolve_automake_var(&vars, &libraries_var) {
                if !val.am_cond.is_empty() {
                    continue;
                }
                let lib = match val.value {
                    AmVoL::Var(_) => continue,
                    AmVoL::Lit(lit) => lit,
                };
                if !lib.ends_with(".la") {
                    continue;
                }
                let name = lib.replace(".", "_");
                let target = self.automake_new_target(
                    name.as_str(),
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
                    AmVoL::Var(_) => continue,
                    AmVoL::Lit(lit) => lit,
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
        dbg!(&automake);
        automake
    }

    fn automake_new_target(
        &self,
        name: &str,
        vars: &HashMap<String, Vec<AmValue<AmWord>>>,
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
                sources.insert(AmValue {
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
        vars: &'a HashMap<String, Vec<AmValue<AmWord>>>,
        var: &'a str,
    ) -> Vec<AmValue<AmVoL>> {
        let mut result = Vec::new();
        if let Some(vals) = vars.get(var) {
            for val in vals {
                // TODO: support concatenated word
                if let Some(lit) = as_single(&val.value)
                    .and_then(as_shell)
                    .and_then(as_literal)
                {
                    result.push(AmValue {
                        value: AmVoL::Lit(lit.to_owned()),
                        am_cond: val.am_cond.clone(),
                    });
                } else if let Some(var) = as_am(&val.value).and_then(as_am_var) {
                    result.extend(self.resolve_automake_var(vars, var));
                } else if let Some(template) = as_am(&val.value).and_then(as_template) {
                    result.push(AmValue {
                        value: AmVoL::Var(template.to_owned()),
                        am_cond: Default::default(),
                    })
                }
            }
        } else {
            result.push(AmValue {
                value: AmVoL::Var(var.to_owned()),
                am_cond: Default::default(),
            });
        }
        result
    }

    fn resolve_automake_path<'a>(
        &self,
        vars: &'a HashMap<String, Vec<AmValue<AmWord>>>,
        var: &'a str,
        base_dir: Option<&Path>,
        built_sources: &[PathBuf],
    ) -> HashSet<AmValue<PathBuf>> {
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
                AmVoL::Var(var) => {
                    result.extend(
                        self.resolve_var(&var, None, false)
                            .into_iter()
                            .map(|value| PathBuf::from(value))
                            .flat_map(|path| find_files(path))
                            .map(|path| AmValue {
                                value: path,
                                am_cond: Default::default(),
                            }),
                    );
                }
                AmVoL::Lit(lit) => result.extend(find_files(PathBuf::from(lit)).into_iter().map(
                    |path| AmValue {
                        value: path,
                        am_cond: val.am_cond.clone(),
                    },
                )),
            }
        }
        result
    }

    fn resolve_automake_identifier(&self, ident: &AmWord) -> Vec<String> {
        let resolve_word = |w: &MayAm<_, _>| match w {
            MayAm::Shell(w) => {
                if let Some(lit) = as_literal(w) {
                    return HashSet::from([lit.to_owned()]);
                } else {
                    Default::default()
                }
            }
            MayAm::Automake(AmVar::Template(template)) => self.resolve_var(&template, None, false),
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
        vars: &mut HashMap<String, Vec<AmValue<AmWord>>>,
    ) {
        nodes.get_mut(id).unwrap().info.condition = conds.clone();
        match nodes.get(id).unwrap().cmd.clone() {
            AmLine::Assignment(assign) => {
                let values = assign
                    .rhs
                    .iter()
                    .map(|w| AmValue {
                        value: w.clone(),
                        am_cond: conds.clone(),
                    })
                    .collect::<Vec<_>>();
                for name in self.resolve_automake_identifier(&assign.lhs) {
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
                conds.push(AmGuard {
                    negated: false,
                    var: var.clone(),
                });
                for id in conditional.then.iter() {
                    self.analyze_automake_variables(*id, nodes, conds, vars);
                }
                conds.pop();
                conds.push(AmGuard {
                    negated: false,
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

    fn read_automake_file(&self, path: &Path) -> String {
        std::fs::read_to_string(path)
            .expect("Reading a file has failed.")
            .replace("$U", "")
    }

    fn extract_source_and_header_files(&mut self) {
        for (_, file) in self.automake.as_ref().unwrap().files.iter() {
            // file.libraries
        }
    }
}
