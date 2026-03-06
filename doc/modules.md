# Module Reference

All modules grouped by pipeline phase. For each module: purpose, key types/functions, and source file path.

## Entry Point & Orchestration

### `main.rs`

CLI entry point using `clap`. Parses command-line arguments, constructs `AnalyzerOptions`, and delegates to `analysis::analysis()`.

**Key types:** `Args` (clap struct with `configure_path`, `output_dir`, `full_script`, `no_type_inference`, `chunk_window_size`, `flatten_threshold`)

### `analysis.rs`

Pipeline orchestration. Creates `Analyzer`, runs async stages (build option LLM analysis, translation), and writes all output files.

**Key functions:**
- `analysis(configure_path, output_dir, options)` — The top-level pipeline entry. In debug mode, prints chunks and exits. In release mode: runs build option analysis, collects project info, translates, generates `Cargo.toml` / `build.rs` / `wrapper.h` / conditional compilation map, and exports evaluation records.

## Display & Utilities

### `display.rs`

`AutoconfPool<U>` — A pool of autoconf AST nodes that implements `NodePool` for pretty-printing. Handles cross-boundary display when chunks split nested structures.

### `utils.rs`

Path helpers and file extension checks (`is_c_extension`, `is_h_extension`, `normalize_path`).

### `utils/glob.rs`

`glob_enumerate(pattern)` — Enumerates concrete strings matching a shell glob pattern (used for build option value candidate extraction).

### `utils/enumerate.rs`

`enumerate_combinations(sets)` — Computes the Cartesian product of a vector of string sets. Used by value set analysis to enumerate all possible dynamic identifier values.

### `utils/llm_analysis.rs`

`LLMAnalysis` trait — Generic interface for LLM-based analyses. Provides `run_llm_analysis()` with retry logic, input/output/evidence type parameters, and cost/duration tracking.

## Core Analyzer

### `analyzer.rs`

Central module containing the `Analyzer` struct, `NodeInfo`, `AstVisitor` trait, `AnalyzerOptions`, and `ProjectMetadata`.

**Key types:**

- **`Analyzer`** — Owns all analysis state. Constructor (`new()`) runs Phases 1-2. Key methods: `translate()`, `generate_cargo_toml()`, `print_build_rs()`, `generate_wrapper_header()`, `print_conditional_compilation_map()`.
- **`NodeInfo`** — Per-node metadata: IDs, parent/child links, chunk assignment, execution order, variable def-use maps, dependency edges.
- **`AstVisitor`** — Trait with `visit_*` / `walk_*` methods for AST traversal. Override `visit_*` to intercept; call `walk_*` to continue recursion.
- **`AnalyzerOptions`** — Configuration: `flatten_threshold`, `chunk_window_size`, `type_inference`, `use_llm`, cache toggles, `rename_rust_functions`.
- **`ProjectMetadata`** — Name, version, bug_report, tarname, URL from `AC_INIT`.

**Key type aliases:**
- `VariableMap = HashMap<String, Vec<Location>>`
- `NodeDependencyMap = HashMap<NodeId, HashSet<String>>`
- `Node = autotools_parser::ast::node::Node<AcCommand, NodeInfo>`

## Phase 1 Modules

### `macro_call.rs`

`MacroFinder` — AstVisitor that records all M4 macro invocations. Collects `(NodeId, M4Macro)` pairs indexed by macro name.

**Key types:** `FixedMacroSideEffect` — Records shell variables and CPP symbols affected by known macros.

### `macro_call/macros_list.rs`

Database of 600+ M4 macro signatures. Each entry specifies argument types, variable side effects (define/use/substitute), and CPP symbol outputs. Used by `MacroFinder` and `VariableAnalyzer` to understand macro behavior.

### `flatten.rs`

`Flattener::flatten(analyzer, threshold)` — Walks the AST and promotes children of nodes with more than `threshold` descendants to top-level. Flattened nodes retain their `parent` link but get their own `top_id`, enabling independent chunk assignment.

## Phase 2 Modules

### `variable.rs`

`VariableAnalyzer` — AstVisitor that tracks variable definitions, usages, and bindings per node. Handles special cases:

- Eval assignments: parses `eval "LHS=RHS"` to extract `Identifier` and `ValueExpr`
- M4 macro side effects: reads variable effects from macro signatures
- Propagated definitions: detects variables defined in all branches of a conditional

**Key types:**
- `Identifier` — Variable name reference: `Name(String)`, `Indirect(String)`, `Concat(Vec<Identifier>)`
- `ValueExpr` — Value expression: `Lit`, `Var`, `Concat`, `DynName`, `Shell`

**Key functions:**
- `VariableAnalyzer::analyze_variables(analyzer)` — Runs the visitor
- `Analyzer::aggregate_def_use()` — Builds global maps and dependency edges
- `Analyzer::remove_unused_variables()` — Cleans up dead assignments

### `value_set_analysis.rs`

Backward dataflow analysis for dynamic identifiers.

**Key types:**
- `Chain` — Backward traversal state: identifier, location, resolved literals, unresolved expressions
- `DividedVariable` — Records how a dynamic identifier (e.g., `${prefix}_${key}`) maps to concrete variable names
- `IdentifierDivision` — Component-to-value mapping for one eval site
- `VSACache` — Persistent cache of resolved identifiers and value expressions

**Key functions:**
- `Analyzer::run_value_set_analysis()` — Entry point. Iterates eval assignments, resolves identifiers, caches results
- `resolve_var(name, loc)` — Resolves a variable to its set of possible literal values at a given location
- `resolve_value_expression(value, loc)` — Resolves any `ValueExpr` to literals
- `construct_chain(name, loc)` — Backward traversal building a `Chain`

### `type_inference.rs`

`TypeInferrer` — AstVisitor that collects `TypeHint` values from usage patterns and resolves them to `DataType`.

**Key types:**
- `DataType` — `Boolean`, `Integer`, `List(Box<DataType>)`, `Path`, `Optional(Box<DataType>)`, `Literal`, `Either(Box<DataType>, Vec<String>)`
- `TypeHint` — `CanBeBoolLike`, `CanBeNum`, `CanContainWhitespace`, `Iterated`, `AppendedSelf`, `UsedAsPath`, `Calculated`, `SizeComparison`, etc.

**Key functions:**
- `TypeInferrer::run_type_inference(analyzer)` — Visits AST, collects hints, resolves types, propagates across variable assignments
- `Analyzer::get_data_type(name)` — Returns inferred type or `Literal` default

### `guard.rs`

Guard condition modeling and analysis.

**Key types:**
- `Guard` — Recursive enum: `N(negated, Atom)`, `And(Vec)`, `Or(Vec)`
- `Atom` — Condition atoms: `Var`, `Arg`, `Arch`, `Os`, `Cpu`, `Env`, `Abi`, `PathExists`, `HasProgram`, `HasLibrary`, `HasHeader`, `Compiler`, `BigEndian`, `Tautology`
- `VarCond` — Variable condition: `True`, `False`, `Empty`, `Eq(VoL)`, `Match(glob)`, `MatchAny`
- `Block` — Group of nodes under same guards, with parent node reference

**Key functions:**
- `GuardAnalyzer::analyze_blocks(analyzer)` — Builds block structure from AST
- `cmp_guards(a, b)` — Partial order on guard sequences (subsumption check)

### `build_option.rs`

Build option analysis and Cargo feature construction.

**Key types:**
- `BuildOption` — An `AC_ARG_ENABLE`/`AC_ARG_WITH` instance: option name, associated variables, value candidates, declaration, related nodes, context
- `BuildOptionInfo` — Aggregated info: all options, arg-var-to-option mapping, feature dependencies, cargo features
- `CargoFeature` — Name, original option, value map, default state
- `FeatureState` — Positive (feature on) or negative (feature off)

**Key functions:**
- `run_build_option_analysis()` — Synchronous analysis: extraction, guard conversion, value collection, context gathering, declaration removal
- `run_extra_build_option_analysis()` — Async LLM-based: value partitioning, Cargo feature construction, caching

### `build_option/use_llm.rs`

LLM integration for build option value partitioning. Implements `LLMAnalysis` to determine representative values, aliases, and defaults for each build option.

**Key types:** `BuildOptionLLMAnalysisResult` — Option name, representatives, aliases, default state.

### `pkg_config.rs`

External library dependency resolution.

**Key types:**
- `PkgConfigAnalyzer` — Stores analyzed `PKG_CHECK_MODULES` calls, discovered packages, and header files
- `SystemPackageManager` trait — Interface for system package managers (`AptPackageManager` implementation)

**Key functions:**
- `consume_pkg_config_macros()` — Processes PKG_CHECK_MODULES, queries pkg-config, discovers headers
- `get_function_definition_bindgen()` — Returns the `run_bindgen()` helper function definition

### `automake.rs`

Makefile.am analysis.

**Key types:**
- `AutomakeAnalyzer` — Parsed automake data: targets, source files, conditionals, variable assignments
- `AmTarget` — Build target with sources, links, dependencies, flags

**Key functions:**
- `analyze_automake_files()` — Parses all `Makefile.am` files in the project
- `consume_automake_macros()` — Processes AM_CONDITIONAL and related macros

### `platform_support.rs`

Platform detection and target triple mapping. Maintains sets of platform-related variables and maps autoconf host/target patterns to Rust `cfg` attributes.

### `dictionary.rs`

Dynamic variable patterns mapped to `HashMap` structures.

**Key types:**
- `DictionaryInstance` — A family of variables with common prefix/suffix structure, accessed as key-value pairs
- `DictionaryAccess` — Single access: operation (Read/Write), keys, raw variable name, assigned value
- `DictionaryKey` — `Lit(String)` or `Var(String)`
- `DictionaryValue` — `Lit(String)`, `Var(String, Location)`, or `Dict(String, Location)`

### `project_info.rs`

`ProjectInfo` — Collected information about the project directory structure: C source files, header files, config template files, substitution files, automake files, build artifacts, generated files.

### `filtering.rs`

`filter_out_commands()` — Removes AST nodes that don't affect build configuration (messages, cleanup, etc.).

### `removal.rs`

`remove_node(node_id)` — Removes a node from the AST pool, updating parent/child relationships and variable maps.

## Phase 3 Modules

### `chunk.rs`

Script decomposition into translatable fragments.

**Key types:**
- `Chunk` — Fragment: nodes, descendant set, parent/children, line range, I/O signature
- `ChunkIO` — Imported/exported variables, bound variables, dictionary accesses, arg vars
- `Scope` — Variable scope within chunk tree: owner, bound_by, writers, overwriters, readers, post_order
- `FunctionSkeleton` — Typed function signature: args, maps, declared, bound_in_loop, return_to_bind, return_to_overwrite, pass_through_args/maps
- `ChunkTree` — Hierarchical chunk structure

**Key functions:**
- `construct_chunks(window, disrespect_assignment)` — Speculative lookahead fusing algorithm
- `cut_variable_scopes_chunkwise()` — Scope analysis across chunks
- `construct_chunk_skeletons()` — Builds `FunctionSkeleton` per chunk
- `print_chunk_skeleton_signature(id)` — Renders Rust function signature

### `translator.rs`

Translation orchestration.

**Key types:**
- `TranslationResult` — All generated code: env_init, default_init, subst_to_cpps, src_incl_conds, recording, bindgen, main_function_body, chunk_funcs
- `ChunkTranslationOutput` — Either `Inlined(InlinedTranslationOutput)` or `LLM(LLMBasedTranslationOutput)`
- `ChunkTranslationMeta` — Metrics: chunk size, translation type, success, cost, duration, retries

**Key functions:**
- `translate()` — Main entry: orchestrates inlined and LLM translations, assembles `TranslationResult`
- `translate_chunks()` — Processes all chunks: inlined first, then LLM in topological order
- `print_build_rs(result, record_path)` — Renders the complete `build.rs` file
- `generate_cargo_toml()` — Renders `Cargo.toml`

### `translator/pretranslation.rs`

Rule-based macro-to-Rust translations for known patterns:

- `AC_CHECK_SIZEOF` → `check_sizeof(type_name)` call
- `AC_CHECK_TYPE` / `AC_CHECK_TYPES` → `check_type(type_name)` call
- `AC_INIT` → `get_function_body_ac_init()`
- `AM_INIT_AUTOMAKE` → `get_function_body_am_init_automake()`

### `translator/use_llm.rs`

LLM-based translation engine.

**Key types:**
- `LLMBasedTranslationInput` — Chunk ID, script text, skeleton, required functions
- `LLMBasedTranslationOutput` — Chunk ID, Rust function name, Rust function body
- `LLMBasedTranslationEvidence` — Validation context: snippets, features, predefinition, signature, banned patterns, code placeholders
- `LLMUser` — Implements `LLMAnalysis` trait for translation
- `LLMValidationFunc` — `Box<dyn Fn(&str) -> Option<String>>` for custom validation

**Key functions:**
- `run_llm_analysis(inputs, max_retries)` — Processes all chunks through LLM with validation
- `get_predefinition(required_funcs)` — Returns Rust source for helper functions (check_header, check_library, define_cfg, etc.)
- `get_rust_check_dir()` — Temporary directory for `cargo check` validation

### `translator/printer.rs`

`TranslatingPrinter` — Converts AST nodes to Rust-like code for LLM prompt construction.

**Key types:**
- `TranslatingPrinter` — Stateful printer with analyzer reference, cursor tracking, branch tracking, indentation
- `FuncRequests` — Tracks which helper functions are needed (check_header, check_library, pkg_config, etc.)

**Key functions:**
- `print_node(node_id)` — Renders a single node to Rust-like code
- `display_guard(guard)` — Renders a guard condition as a Rust boolean expression
- `get_required_snippets()` — Returns strings that must appear in the LLM output
- `get_banned_patterns()` — Returns patterns that indicate hallucination
- `get_embedded_chunks()` — Returns child chunk references for dependency tracking
- `display_var_as_rust_str(var, data_type)` — Formats a variable reference for string context

## Phase 4 Modules

### `conditional_compilation.rs`

C preprocessor to Rust `cfg` mapping.

**Key types:**
- `ConditionalCompilationMap` — Three maps: `cpp_map` (CPP symbol → policy), `subst_to_cpp_map` (AC_SUBST var → policy), `src_incl_map` (source file → inclusion conditions)
- `CCMigraionPolicy` — Migration type + key + optional value
- `CCMigrationType` — `Cfg`, `Env`, `Fixed`, `Set`, `Unset`
- `SourceInclusionCondition` — AM conditional name, cfg key, negation flag

**Key functions:**
- `create_conditional_compilation_map()` — Scans config.h.in templates, matches CPP symbols to autoconf variables
- `print_conditional_compilation_map()` — Serializes to JSON

### `record.rs`

Evaluation data collection and export.

**Key types:**
- `RecordCollector` — Accumulates analysis metrics with timing
- `RecordData` — Top-level: project info, timing, build options, chunks
- `ProjectAnalysisRecord` — Files, commands, chunks, parameters
- `BuildOptionAnalysisRecord` — Per-option: success, cost, duration, features
- `ChunkAnalysisRecord` — Per-chunk: type, success, cost, duration, retries
- `TimingRecord` — Duration breakdown by stage
- `TranslationType` — `Inlined` or `LLMAssisted`
- `AnalysisParameters` — Chunk window, type inference, build option analysis settings

**Key functions:**
- `export_project_info_json(path)` — Writes project info
- `export_build_options_csv(path)` — Writes per-option metrics
- `export_chunks_csv(path)` — Writes per-chunk metrics

### `location.rs`

Execution-order-aware positions.

**Key types:**
- `Location` — `{ node_id, exec_id, order_in_expr, line }`, implements `Ord` for comparison
- `ExecId = usize` — Global execution counter

**Key functions:**
- `Analyzer::get_location_of_node_start(id)` / `get_location_of_node_end(id)` — Boundary locations for range comparisons
