use std::{
    collections::HashMap,
    path::{Path, PathBuf},
};

use autotools_parser::{
    ast::{
        am::{AmAssignOp, AmLine, AmWord, MayAm},
        builder::AutomakeNodeBuilder,
        minimal::Word,
        node::{Node, NodeId, WordFragment},
    },
    lexer::Lexer,
    parse::automake::AutomakeParser,
};
use slab::Slab;

use super::Analyzer;

type AmNode = Node<AmLine, AmNodeInfo>;

/// Represents a node extension in the dependency graph
#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct AmNodeInfo {
    node_id: NodeId,
}

#[allow(dead_code)]
#[derive(Debug, Clone, Default)]
struct AmTarget {
    name: String,
    // program_SOURCES, EXTRA_program_SOURCES,
    sources: Vec<AmValue<AmWord>>,
    // program_LIBADD, program_LDADD,
    links: Vec<AmValue<AmWord>>,
    // program_DEPENDENCIES, EXTRA_program_DEPENDENCIES,
    dependencies: Vec<AmValue<AmWord>>,
    // program_LDFLAGS
    ldflags: Option<Vec<AmWord>>,
    // program_AR
    cmd_ar: Option<Vec<AmWord>>,
    // program_LINK
    cmd_link: Option<Vec<AmWord>>,
    // program_CFLAGS
    cflags: Option<Vec<AmWord>>,
    // program_CCASFLAGS
    ccasflags: Option<Vec<AmWord>>,
    // program_CPPFLAGS
    cppflags: Option<Vec<AmWord>>,
    // program_CXXFLAGS
    cxxflags: Option<Vec<AmWord>>,
    // program_SHORTNAME
    shortname: Option<AmWord>,
}

#[allow(dead_code)]
#[derive(Debug, Clone, Default)]
struct Automake {
    this_path: PathBuf,
    include_paths: Vec<PathBuf>,
    sub_paths: Vec<PathBuf>,
    programs: HashMap<String, Vec<AmTarget>>,
    libraries: HashMap<String, Vec<AmTarget>>,
    headers: HashMap<String, Vec<AmValue<String>>>,
    data: HashMap<String, Vec<AmValue<String>>>,
    dirs: HashMap<String, AmValue<AmWord>>,
    extra_dist: Vec<String>,
    built_sources: Vec<String>,
}

#[allow(dead_code)]
#[derive(Debug, Clone)]
struct AmValue<T> {
    value: T,
    condition: Vec<AmGuard>,
}

#[allow(dead_code)]
#[derive(Debug, Clone)]
struct AmGuard {
    negated: bool,
    var: String,
}

#[derive(Debug, Clone, Default)]
pub(crate) struct AutomakeAnalyzer {
    files: HashMap<PathBuf, Automake>,
}

fn as_shell(word: &AmWord) -> Option<&WordFragment<AmWord>> {
    if let Word::Single(MayAm::Shell(shell_word)) = &word.0 {
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

impl Analyzer {
    pub(crate) fn automake(&self) -> &AutomakeAnalyzer {
        self.automake.as_ref().unwrap()
    }

    pub(crate) fn automake_mut(&mut self) -> &mut AutomakeAnalyzer {
        self.automake.as_mut().unwrap()
    }

    pub(crate) fn analyze_automake_files(&mut self) {
        self.automake.replace(Default::default());

        for path in self.project_info.am_files.clone() {
            let automake = self.analyze_automake_file(&path);
            self.automake_mut().files.insert(path.into(), automake);
        }
        let files = self.automake().files.keys().cloned().collect::<Vec<_>>();
        self.project_info.am_files.extend(files);
    }

    fn analyze_automake_file(&mut self, path: &Path) -> Automake {
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
        let contents = read_automake_file(&path);
        let lexer = Lexer::new(contents.chars());
        let (nodes, top_ids) =
            AutomakeParser::<_, AutomakeNodeBuilder<AmNodeInfo>>::new(lexer).parse_all();
        let nodes = nodes
            .into_iter()
            .map(|(node_id, mut n)| {
                n.info.node_id = node_id;
                (node_id, n)
            })
            .collect::<Slab<AmNode>>();
        let mut vars = HashMap::new();
        let mut automake = Automake::default();
        automake.this_path = path.clone();
        for id in top_ids.iter() {
            automake_analyze_variables(*id, &nodes, &mut Vec::new(), &mut vars);
            if let Some(AmLine::Include(w)) = nodes.get(*id).map(|n| &n.cmd) {
                if let Word::Single(MayAm::Shell(WordFragment::Literal(lit))) = &w.0 {
                    let relative = PathBuf::from(lit);
                    if let Some(include_path) = resolve_path(&relative) {
                        automake.include_paths.push(include_path.clone());
                        if !self.automake().files.contains_key(&include_path) {
                            let res = self.analyze_automake_file(&include_path);
                            self.automake_mut().files.insert(include_path, res);
                        }
                    }
                }
            }
        }
        if let Some(vals) = vars.get("SUBDIRS") {
            for val in vals {
                if let Some(lit) = as_shell(&val.value).and_then(as_literal) {
                    let relative = PathBuf::from(lit).join("Makefile.am");
                    if let Some(sub_path) = resolve_path(&relative) {
                        automake.sub_paths.push(sub_path.clone());
                        if !self.automake().files.contains_key(&sub_path) {
                            let res = self.analyze_automake_file(&sub_path);
                            self.automake_mut().files.insert(sub_path, res);
                        }
                    }
                }
            }
        }
        automake
    }
}

fn automake_analyze_variables(
    id: NodeId,
    nodes: &Slab<AmNode>,
    conds: &mut Vec<AmGuard>,
    vars: &mut HashMap<String, Vec<AmValue<AmWord>>>,
) {
    match &nodes.get(id).unwrap().cmd {
        AmLine::Assignment(assign) => {
            let name = assign.lhs.clone();
            let values = assign
                .rhs
                .iter()
                .map(|w| AmValue {
                    value: w.clone(),
                    condition: conds.clone(),
                })
                .collect::<Vec<_>>();
            match &assign.op {
                AmAssignOp::Instant | AmAssignOp::Lazy => {
                    vars.insert(name, values);
                }
                AmAssignOp::Append => {
                    vars.entry(assign.lhs.clone())
                        .or_insert_with(Vec::new)
                        .extend(values);
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
                automake_analyze_variables(*id, nodes, conds, vars);
            }
            conds.pop();
            conds.push(AmGuard {
                negated: false,
                var: var.clone(),
            });
            for id in conditional.otherwise.iter() {
                automake_analyze_variables(*id, nodes, conds, vars);
            }
            conds.pop();
        }
        _ => (),
    }
}

fn read_automake_file(path: &Path) -> String {
    std::fs::read_to_string(path)
        .expect("Reading a file has failed.")
        .replace("$U", "")
}
