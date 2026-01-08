use std::{
    collections::{HashMap, HashSet},
    env,
    fmt::Debug,
    fs,
    hash::{DefaultHasher, Hash, Hasher},
    path::{Path, PathBuf},
    process::Command,
};

use bincode::{Decode, Encode};

use autotools_parser::ast::{minimal::WordFragment, node::NodeId, Parameter};
use itertools::Itertools;

use crate::{
    analyzer::{as_literal, as_shell, guard::VoL, Analyzer},
    utils::is_h_extension,
};

/// Trait for system package managers to resolve package dependencies
trait SystemPackageManager: Debug {
    /// Get the system package that owns a given .pc file
    fn get_package_for_pc_file(&self, pc_file_name: &Path) -> Result<String, PkgConfigError>;

    /// Get all header files provided by a system package
    fn get_package_headers(&self, package_name: &str) -> Result<Vec<PathBuf>, PkgConfigError>;

    /// Check if the system package manager is available
    fn is_available(&self) -> bool;

    /// Sanitize a package name to be a valid C/Rust identifier
    fn sanitize_package_name(&self, s: &str) -> String;

    /// return package installation command for instruction
    fn install_command(&self) -> &'static str;
}

/// APT-based system package manager (Ubuntu/Debian)
#[derive(Debug, Default)]
struct AptPackageManager;

impl SystemPackageManager for AptPackageManager {
    fn get_package_for_pc_file(&self, pc_file_name: &Path) -> Result<String, PkgConfigError> {
        let output = Command::new("apt-file")
            .arg("search")
            .arg(pc_file_name)
            .output()
            .map_err(|e| {
                PkgConfigError::SystemPackageManagerError(format!("apt-file command failed: {}", e))
            })?;

        if !output.status.success() {
            return Err(PkgConfigError::SystemPackageNotFound(
                pc_file_name.to_str().unwrap().to_owned(),
            ));
        }

        let stdout = String::from_utf8_lossy(&output.stdout);
        let package_name = stdout
            .lines()
            .next()
            .and_then(|line| line.split(':').next())
            .ok_or_else(|| {
                PkgConfigError::SystemPackageManagerError("Invalid apt-file output".into())
            })?;

        // check if the package is installed
        let output = Command::new("dpkg")
            .arg("-s")
            .arg(&package_name)
            .output()
            .map_err(|e| {
                PkgConfigError::SystemPackageManagerError(format!("dpkg command failed: {}", e))
            })?;

        if !output.status.success() {
            return Err(PkgConfigError::SystemPackageNotInstalled(
                self.install_command().to_owned(),
                package_name.to_owned(),
            ));
        }

        Ok(package_name.to_string())
    }

    fn get_package_headers(&self, package_name: &str) -> Result<Vec<PathBuf>, PkgConfigError> {
        let output = Command::new("apt-file")
            .arg("list")
            .arg(package_name)
            .output()
            .map_err(|e| {
                PkgConfigError::SystemPackageManagerError(format!("apt-file list failed: {}", e))
            })?;

        if !output.status.success() {
            return Err(PkgConfigError::SystemPackageManagerError(
                "apt-file list command failed".into(),
            ));
        }

        let stdout = String::from_utf8_lossy(&output.stdout);
        let headers: Vec<PathBuf> = stdout
            .lines()
            .filter_map(|line| {
                // apt-file output format: "package: /path/to/file"
                let path_part = line.split(':').nth(1)?.trim();
                let path = PathBuf::from(path_part);
                if path.extension().map_or(false, |ext| is_h_extension(ext)) {
                    Some(path)
                } else {
                    None
                }
            })
            .collect();

        Ok(headers)
    }

    fn is_available(&self) -> bool {
        Command::new("apt-file").arg("--help").output().is_ok()
    }

    fn sanitize_package_name(&self, s: &str) -> String {
        let s = s.strip_prefix("lib").unwrap_or(s);
        let s = s.strip_suffix("-dev").unwrap_or(s);
        s.chars()
            .map(|c| {
                if c.is_ascii_alphanumeric() || c == '_' {
                    c.to_ascii_uppercase()
                } else {
                    '_'
                }
            })
            .collect()
    }

    fn install_command(&self) -> &'static str {
        "sudo apt install"
    }
}

/// Error types for pkg-config operations
#[derive(Debug)]
pub(super) enum PkgConfigError {
    PkgConfigCommandError(String),
    SystemPackageManagerError(String),
    SystemPackageNotFound(String),
    SystemPackageNotInstalled(String, String),
    CompilerDetectionError(String),
    IoError(std::io::Error),
}

impl std::fmt::Display for PkgConfigError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PkgConfigError::PkgConfigCommandError(msg) => {
                write!(f, "pkg-config command failed: {}", msg)
            }
            PkgConfigError::SystemPackageManagerError(msg) => {
                write!(f, "System package manager error: {}", msg)
            }
            PkgConfigError::SystemPackageNotFound(pc) => {
                write!(f, "System Package not found that includes: {}", pc)
            }
            PkgConfigError::SystemPackageNotInstalled(installation, pkg) => {
                write!(
                    f,
                    "Found System Packages not installed. Retry after executing: {} {}",
                    installation, pkg
                )
            }
            PkgConfigError::CompilerDetectionError(msg) => {
                write!(f, "Compiler detection error: {}", msg)
            }
            PkgConfigError::IoError(e) => write!(f, "IO error: {}", e),
        }
    }
}

impl std::error::Error for PkgConfigError {}

impl From<std::io::Error> for PkgConfigError {
    fn from(error: std::io::Error) -> Self {
        PkgConfigError::IoError(error)
    }
}

/// Trait for querying system default include paths
trait SystemIncludePathProvider: Debug {
    /// Get default include paths from the system
    fn get_default_include_paths(&self) -> Result<Vec<PathBuf>, PkgConfigError>;

    /// Check if this provider is available on the current system
    fn is_available(&self) -> bool;
}

/// Windows MSVC include path provider using INCLUDE environment variable
#[derive(Debug, Default)]
struct MsvcIncludeProvider;

impl SystemIncludePathProvider for MsvcIncludeProvider {
    fn get_default_include_paths(&self) -> Result<Vec<PathBuf>, PkgConfigError> {
        env::var("INCLUDE")
            .map_err(|e| {
                PkgConfigError::CompilerDetectionError(format!("INCLUDE env var not found: {}", e))
            })
            .map(|include_paths| {
                include_paths
                    .split(';')
                    .filter(|path| !path.is_empty())
                    .map(PathBuf::from)
                    .collect()
            })
    }

    fn is_available(&self) -> bool {
        cfg!(windows) && env::var("INCLUDE").is_ok()
    }
}

/// Unix compiler include path provider using compiler introspection
#[derive(Debug)]
struct UnixCompilerIncludeProvider {
    compiler: String,
}

impl UnixCompilerIncludeProvider {
    fn new(compiler: &str) -> Self {
        Self {
            compiler: compiler.to_string(),
        }
    }
}

impl SystemIncludePathProvider for UnixCompilerIncludeProvider {
    fn get_default_include_paths(&self) -> Result<Vec<PathBuf>, PkgConfigError> {
        let output = Command::new(&self.compiler)
            .args(&["-E", "-v", "-"])
            .arg("/dev/null")
            .output()
            .map_err(|e| {
                PkgConfigError::CompilerDetectionError(format!(
                    "Failed to run compiler {}: {}",
                    self.compiler, e
                ))
            })?;

        if !output.status.success() {
            return Err(PkgConfigError::CompilerDetectionError(format!(
                "Compiler {} failed with exit code: {}",
                self.compiler, output.status
            )));
        }

        // Parse compiler output to extract include paths
        // GCC/Clang output format includes lines like:
        // #include <...> search starts here:
        // /usr/include
        // /usr/local/include
        // End of search list.
        let stderr = String::from_utf8_lossy(&output.stderr);
        let mut in_include_section = false;
        let mut include_paths = Vec::new();

        for line in stderr.lines() {
            let trimmed = line.trim();
            if trimmed.contains("#include <...> search starts here:") {
                in_include_section = true;
                continue;
            }
            if trimmed.contains("End of search list") {
                break;
            }
            if in_include_section && !trimmed.is_empty() && !trimmed.starts_with('#') {
                include_paths.push(PathBuf::from(trimmed));
            }
        }

        if include_paths.is_empty() {
            Err(PkgConfigError::CompilerDetectionError(format!(
                "No include paths found in compiler {} output",
                self.compiler
            )))
        } else {
            Ok(include_paths)
        }
    }

    fn is_available(&self) -> bool {
        Command::new(&self.compiler)
            .arg("--version")
            .output()
            .map(|output| output.status.success())
            .unwrap_or(false)
    }
}

/// Default system include path detector
#[derive(Debug)]
struct SystemIncludeDetector {
    providers: Vec<Box<dyn SystemIncludePathProvider>>,
}

impl SystemIncludeDetector {
    fn new() -> Self {
        let mut providers: Vec<Box<dyn SystemIncludePathProvider>> = Vec::new();

        // Add MSVC provider for Windows
        let msvc_provider = MsvcIncludeProvider;
        if msvc_provider.is_available() {
            providers.push(Box::new(msvc_provider));
        }

        // Add common Unix compilers
        for compiler in &["gcc", "clang", "cc"] {
            let provider = UnixCompilerIncludeProvider::new(compiler);
            if provider.is_available() {
                providers.push(Box::new(provider));
                break; // Use first available compiler
            }
        }

        Self { providers }
    }

    fn get_default_include_paths(&self) -> Result<Vec<PathBuf>, PkgConfigError> {
        for provider in &self.providers {
            match provider.get_default_include_paths() {
                Ok(paths) => return Ok(paths),
                Err(e) => {
                    eprintln!("Warning: Failed to get include paths from provider: {}", e);
                    continue;
                }
            }
        }

        Err(PkgConfigError::CompilerDetectionError(
            "No working include path provider found".to_string(),
        ))
    }
}

/// Maps C headers to their pkg-config packages
#[derive(Debug, Clone, Default, Encode, Decode)]
pub(super) struct SystemPackageInfo {
    /// system package name (not the one of pkg-config)
    pub system_package_name: String,
    /// derived include guard name
    pub include_guard_macro_name: String,
    /// its header files used in the target project
    pub headers: Vec<PathBuf>,
    /// include paths from pkg-config
    pub include_paths: Vec<PathBuf>,
}

/// Main analyzer for pkg-config dependencies
#[derive(Debug)]
pub(super) struct PkgConfigAnalyzer {
    pub pkg_check_modules_calls: HashMap<NodeId, PkgCheckModulesInfo>,
    system_package_manager: Box<dyn SystemPackageManager>,
    system_include_paths: Vec<PathBuf>,
    pc_to_sys_pkg: HashMap<String, String>,
    system_packages: HashMap<String, SystemPackageInfo>,
    use_cache: bool,
}

impl PkgConfigAnalyzer {
    /// Create a new PkgConfigAnalyzer with automatic system package manager detection
    pub fn new(
        pkg_check_modules_calls: HashMap<NodeId, PkgCheckModulesInfo>,
        use_cache: bool,
    ) -> Self {
        let system_package_manager: Box<dyn SystemPackageManager> =
            if AptPackageManager.is_available() {
                Box::new(AptPackageManager)
            } else {
                // Fallback to apt - could add more package managers like homebrew
                Box::new(AptPackageManager)
            };

        let system_include_detector = SystemIncludeDetector::new();
        let system_include_paths = system_include_detector
            .get_default_include_paths()
            .unwrap_or_default();

        Self {
            pkg_check_modules_calls,
            system_package_manager,
            system_include_paths,
            pc_to_sys_pkg: Default::default(),
            system_packages: Default::default(),
            use_cache,
        }
    }

    pub fn run(&mut self) -> Result<(), PkgConfigError> {
        let pc_names = self
            .pkg_check_modules_calls
            .values()
            .flat_map(|info| info.packages.iter().map(|(pc_name, _)| pc_name.to_owned()))
            .collect::<HashSet<_>>();

        // Try to load from cache first
        if let Some((cached_pc_to_sys_pkg, cached_system_packages)) =
            self.load_pkg_config_cache(&pc_names)
        {
            self.pc_to_sys_pkg = cached_pc_to_sys_pkg;
            self.system_packages = cached_system_packages;
            println!(
                "Using cached pkg-config analysis results for {} packages",
                pc_names.len()
            );
            return Ok(());
        }

        let mut not_installed_packages = Vec::new();

        // analyze packages
        for pc_name in &pc_names {
            let info = match self.find_package(pc_name) {
                Err(e @ PkgConfigError::SystemPackageNotFound(_)) => {
                    println!("{}", e);
                    continue;
                }
                Err(PkgConfigError::SystemPackageNotInstalled(_, pkg)) => {
                    not_installed_packages.push(pkg);
                    continue;
                }
                Err(e) => return Err(e),
                Ok(system_package_name) => self.analyze_package(&system_package_name, pc_name)?,
            };
            self.pc_to_sys_pkg
                .insert(pc_name.to_owned(), info.system_package_name.clone());
            self.system_packages
                .insert(info.system_package_name.clone(), info);
        }

        if !not_installed_packages.is_empty() {
            return Err(PkgConfigError::SystemPackageNotInstalled(
                self.system_package_manager.install_command().to_owned(),
                not_installed_packages.join(" "),
            ));
        }

        // Save results to cache
        self.save_pkg_config_cache(&pc_names);

        Ok(())
    }

    /// Find a system package that contains target pkg-config library
    fn find_package(&mut self, pc_name: &str) -> Result<String, PkgConfigError> {
        // Get .pc file location using pkg-config --path
        let pc_file_name = self.get_pc_file_path(pc_name);

        // Get system package name using apt-file search
        let system_package_name = self
            .system_package_manager
            .get_package_for_pc_file(&pc_file_name)?;

        Ok(system_package_name)
    }

    fn analyze_package(
        &mut self,
        system_package_name: &str,
        pc_name: &str,
    ) -> Result<SystemPackageInfo, PkgConfigError> {
        let mut ret = self
            .system_packages
            .get(system_package_name)
            .cloned()
            .unwrap_or(SystemPackageInfo {
                system_package_name: system_package_name.to_owned(),
                include_guard_macro_name: {
                    // Generate cpp macro name for conditional compilation
                    format!(
                        "USE_PKG_{}",
                        self.system_package_manager
                            .sanitize_package_name(&system_package_name)
                    )
                },
                headers: Default::default(),
                include_paths: Default::default(),
            });

        // Get headers from system package
        let headers = self
            .system_package_manager
            .get_package_headers(&system_package_name)?;

        // Get include paths from pkg-config
        let include_paths = self.get_pc_library(pc_name).unwrap().include_paths;

        ret.headers.extend(headers);
        ret.include_paths.extend(include_paths);

        Ok(ret)
    }

    pub(super) fn get_system_package_info(&self, pc_name: &str) -> Option<&SystemPackageInfo> {
        self.pc_to_sys_pkg
            .get(pc_name)
            .and_then(|sys_pkg| self.system_packages.get(sys_pkg))
    }

    pub(super) fn get_pkg_check_modules_info(
        &self,
        node_id: NodeId,
    ) -> Option<&PkgCheckModulesInfo> {
        self.pkg_check_modules_calls.get(&node_id)
    }

    /// Get the path to a .pc file using pkg-config --path
    fn get_pc_file_path(&self, package_name: &str) -> PathBuf {
        let output = Command::new("pkg-config")
            .arg("--path")
            .arg(package_name)
            .output();

        if output.as_ref().is_ok_and(|o| o.status.success()) {
            PathBuf::from(String::from_utf8_lossy(&output.unwrap().stdout).trim())
        } else {
            PathBuf::from(format!("{}.pc", package_name))
        }
    }

    fn get_pc_library(&self, package_name: &str) -> Option<pkg_config::Library> {
        pkg_config::Config::new()
            .cargo_metadata(false)
            .env_metadata(false)
            .probe(package_name)
            .ok()
    }

    /// Load cached pkg-config analysis results
    fn load_pkg_config_cache(
        &self,
        pc_names: &HashSet<String>,
    ) -> Option<(HashMap<String, String>, HashMap<String, SystemPackageInfo>)> {
        if !self.use_cache {
            return None;
        }

        let cache_path = self.get_pkg_config_cache_path(pc_names);
        if let Ok(content) = fs::read(&cache_path) {
            // Try to decode using bincode
            if let Ok(((pc_to_sys_pkg, system_packages, _), _)) =
                bincode::decode_from_slice::<
                    (
                        HashMap<String, String>,
                        HashMap<String, SystemPackageInfo>,
                        u64,
                    ),
                    bincode::config::Configuration,
                >(&content, bincode::config::standard())
            {
                println!("Loaded pkg-config cache from: {:?}", cache_path);
                return Some((pc_to_sys_pkg, system_packages));
            }
        }
        None
    }

    /// Save pkg-config analysis results to cache
    fn save_pkg_config_cache(&self, pc_names: &HashSet<String>) {
        if !self.use_cache {
            return;
        }

        let cache_path = self.get_pkg_config_cache_path(pc_names);
        if let Some(parent) = cache_path.parent() {
            let _ = fs::create_dir_all(parent);
        }

        // Include a version/hash in the cache to detect changes
        let version_hash = self.compute_cache_hash(pc_names);
        let cache_data = (
            self.pc_to_sys_pkg.clone(),
            self.system_packages.clone(),
            version_hash,
        );

        if let Ok(content) = bincode::encode_to_vec(cache_data, bincode::config::standard()) {
            if let Ok(()) = fs::write(&cache_path, content) {
                println!("Saved pkg-config cache to: {:?}", cache_path);
            }
        }
    }

    /// Get the cache file path for pkg-config analysis
    fn get_pkg_config_cache_path(&self, pc_names: &HashSet<String>) -> PathBuf {
        let h = self.compute_cache_hash(pc_names);
        PathBuf::from(format!("/tmp/pkg_config_cache.{:x}.bin", h))
    }

    /// Compute hash for cache key based on analyzed package names
    fn compute_cache_hash(&self, pc_names: &HashSet<String>) -> u64 {
        let mut hasher = DefaultHasher::new();

        // Sort packages for consistent hashing
        let mut sorted_names: Vec<_> = pc_names.iter().collect();
        sorted_names.sort();

        for name in sorted_names {
            name.hash(&mut hasher);
        }

        hasher.finish()
    }
}

#[derive(Debug, Clone, Encode, Decode)]
pub(crate) struct PkgCheckModulesInfo {
    /// list of probed packages. we support minimum version option.
    /// TODO: support other version specification (maximum, range)
    pub packages: Vec<(String, Option<VoL>)>,
    /// commands executed if the probe succeed
    pub action_if_found: Vec<NodeId>,
    /// commands executed if failed
    pub action_if_not_found: Vec<NodeId>,
    /// name of a defined variable
    pub cflags_var_name: String,
    /// name of a defined variable
    pub libs_var_name: String,
}

impl Analyzer {
    pub(super) fn consume_pkg_config_macros(&mut self) {
        let mut map = HashMap::new();
        let macro_calls = self.macro_calls.as_ref().unwrap();
        for pkg_config_macro in ["PKG_CHECK_MODULES"] {
            if let Some(v) = macro_calls.get(pkg_config_macro) {
                for (node_id, macro_call) in v {
                    // TODO: we are going to extensive analysis of this macro to prepare all for
                    // rule-based translation.

                    let prefix = macro_call.get_arg_as_literal(0).unwrap();
                    let mut words = macro_call.get_arg_as_array(1).unwrap().into_iter();
                    let action_if_found = macro_call.get_arg_as_cmd(2).unwrap_or_default();
                    let action_if_not_found = macro_call.get_arg_as_cmd(3).unwrap_or_default();

                    let mut packages = Vec::new();
                    while let Some(w) = words.next() {
                        if let Some(package_name) =
                            as_shell(&w).and_then(as_literal).map(|s| s.to_owned())
                        {
                            let mut peekable = words.clone().peekable();
                            let peeked_literal =
                                peekable.peek().and_then(as_shell).and_then(as_literal);
                            let has_minimum_version = peeked_literal.is_some_and(|lit| lit == ">=");
                            let has_unsupported_version_requirement = peeked_literal
                                .is_some_and(|lit| matches!(lit, "=" | ">" | "<" | "<="));
                            if has_minimum_version {
                                words.next();
                                let at_least_version = words
                                    .next()
                                    .as_ref()
                                    .and_then(as_shell)
                                    .map(|w| match w {
                                        WordFragment::Literal(lit) => VoL::Lit(lit.into()),
                                        WordFragment::Param(Parameter::Var(var)) => VoL::Var(var.into()),
                                        _ => todo!("Unsupported version representation found in PKG_CHECK_MODULES"),
                                    })
                                    .unwrap();
                                packages.push((package_name, Some(at_least_version)));
                            } else if has_unsupported_version_requirement {
                                todo!("Unsupported version requirement found in PKG_CHECK_MODULES");
                            } else {
                                packages.push((package_name, None));
                            }
                        }
                    }

                    let summary = PkgCheckModulesInfo {
                        packages,
                        action_if_found,
                        action_if_not_found,
                        cflags_var_name: format!("{}_CFLAGS", &prefix),
                        libs_var_name: format!("{}_LIBS", &prefix),
                    };
                    map.insert(*node_id, summary);
                }
            }
        }
        let mut pkg_config_analyzer =
            PkgConfigAnalyzer::new(map, self.options.use_pkg_config_cache);
        match pkg_config_analyzer.run() {
            Ok(_) => (),
            Err(e) => {
                println!("pkg config analysis failed: {}", e);
                std::process::exit(1);
            }
        }

        self.pkg_config_analyzer.replace(pkg_config_analyzer);
    }

    pub(super) fn pkg_config_analyzer(&self) -> &PkgConfigAnalyzer {
        self.pkg_config_analyzer.as_ref().unwrap()
    }

    /// Generate a wrapper.h file for analyzed packages based on project headers
    pub fn generate_wrapper_header(&self) -> Option<String> {
        // Step 1: Build package_to_headers classification map
        let mut package_to_headers: std::collections::HashMap<String, Vec<&std::path::PathBuf>> =
            std::collections::HashMap::new();

        for header in &self.project_info.ext_h_files {
            for (package_name, sys_pkg_info) in &self.pkg_config_analyzer().system_packages {
                for include_dir in sys_pkg_info
                    .include_paths
                    .iter()
                    .chain(&self.pkg_config_analyzer().system_include_paths)
                {
                    let expected_path = include_dir.join(header);
                    if sys_pkg_info.headers.contains(&expected_path) {
                        package_to_headers
                            .entry(package_name.clone())
                            .or_default()
                            .push(header);
                        break; // Found providing package for this header
                    }
                }
            }
        }

        if package_to_headers.is_empty() {
            return None;
        }

        // Step 2: Generate wrapper using classification map
        let mut wrapper_content = String::new();

        wrapper_content.push_str("// Auto-generated wrapper header for external libraries\n");
        wrapper_content.push_str("// Generated by c2cargo\n\n");

        for sys_pkg_info in self
            .pkg_config_analyzer()
            .system_packages
            .values()
            .sorted_by_key(|info| info.include_guard_macro_name.as_str())
        {
            if let Some(headers) = package_to_headers.get(&sys_pkg_info.system_package_name) {
                if !headers.is_empty() {
                    wrapper_content.push_str(&format!(
                        "#ifdef {}\n",
                        sys_pkg_info.include_guard_macro_name
                    ));

                    for header in headers {
                        wrapper_content
                            .push_str(&format!("#include <{}>\n", header.to_str().unwrap()));
                    }

                    wrapper_content.push_str(&format!(
                        "#endif // {}\n\n",
                        sys_pkg_info.include_guard_macro_name
                    ));
                }
            }
        }

        Some(wrapper_content)
    }
}

pub(super) fn get_function_definition_pkg_config() -> &'static str {
    r#"
fn run_pkg_config(package: &str, min_version: Option<&str>) -> Option<pkg_conig::Library> {
  let config = if let Some(min) = min_version {
    pkg_config::Config::new()::at_least_version(min);
  } else {
    pkg_config::Config::new();
  };
  config.probe(package).ok()?
}"#
}

pub(super) fn get_function_definition_bindgen() -> &'static str {
    r#"
fn run_bindgen() {
    let bindings = bindgen::Builder::default()
        // The input header we would like to generate bindings for.
        .header("wrapper.h")
        // Tell cargo to invalidate the built crate whenever any of the included header files changed.
        .parse_callbacks(Box::new(bindgen::CargoCallbacks::new()))
        // Finish the builder and generate the bindings.
        .generate()
        // Unwrap the Result and panic on failure.
        .expect("Unable to generate bindings");

    // Write the bindings to the $OUT_DIR/bindings.rs file.
    let out_path = PathBuf::from(env::var("OUT_DIR").unwrap());
    bindings.write_to_file(out_path.join("bindings.rs")).expect("Couldn't write bindings!");
}
"#
}
