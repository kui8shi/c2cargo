# Architecture

## Overview

c2cargo converts autoconf/automake build systems into Cargo build artifacts through a four-phase pipeline:

```
configure.ac + Makefile.am
       |
  [Phase 1: Normalization & Parsing]
       |
  [Phase 2: Semantic Analysis]
       |
  [Phase 3: Fragment Decomposition & Translation]
       |
  [Phase 4: Cargo Artifact Generation]
       |
  Cargo.toml + build.rs + wrapper.h + conditional compilation map
```

## Core Abstractions

### `Analyzer` (`src/analyzer.rs`)

The central analysis engine. Owns all state and orchestrates every phase:

- **`pool: AutoconfPool<NodeInfo>`** — All AST nodes stored in a `Slab`, indexed by `NodeId`
- **`top_ids: Vec<NodeId>`** — Top-level command sequence (execution order)
- **`blocks: Slab<Block>`** — Conditional branch blocks with guard conditions
- **`chunks: Slab<Chunk>`** — Decomposed script fragments after chunking
- **`options: AnalyzerOptions`** — Configurable thresholds (flatten, chunk window, type inference toggle, LLM toggle, cache settings)
- Various lazily-initialized analysis results: variable maps, type maps, build options, dictionaries, conditional compilation map, etc.

The `Analyzer::new()` constructor runs the entire analysis pipeline synchronously (Phases 1-2), while `translate()` (Phase 3) and artifact generation (Phase 4) are called separately from `analysis::analysis()`.

### `Node` / `NodeInfo` (`src/analyzer.rs`)

Each AST node is a `Node<AcCommand, NodeInfo>` from `autotools-parser`, extended with `NodeInfo`:

- **`node_id`** / **`top_id`** — Self-ID and the ID of the top-most parent (set after flattening)
- **`chunk_id`** — Which chunk this node belongs to
- **`exec_id`** / **`exit`** — Execution order markers for location comparison
- **`parent`** / **`block`** / **`branches`** — Tree structure and conditional branching
- **`definitions`** / **`usages`** / **`bounds`** — Per-node variable def-use information (`VariableMap = HashMap<String, Vec<Location>>`)
- **`dependencies`** / **`dependents`** — Def-use edges to other nodes (`NodeDependencyMap`)
- **`propagated_definitions`** — Variables defined across all branches of a conditional (guaranteed initialization)

### `AstVisitor` trait (`src/analyzer.rs`)

A walker pattern for traversing the AST. Provides default `walk_*` methods that recursively visit children, and `visit_*` methods that can be overridden. Used by:

- `VariableAnalyzer` — Tracks variable definitions and usages
- `TypeInferrer` — Collects type hints from usage patterns
- `MacroFinder` — Records M4 macro call sites
- `GuardAnalyzer` — Builds conditional execution contexts

### `Chunk` / `ChunkIO` / `FunctionSkeleton` (`src/analyzer/chunk.rs`)

A `Chunk` is a decomposed script fragment:

- **`nodes: Vec<NodeId>`** — Top-level nodes in this chunk
- **`descendant_nodes: HashSet<NodeId>`** — All nodes reachable within this chunk
- **`parent`** / **`children`** — Chunk tree for nested control flow
- **`io: ChunkIO`** — I/O signature:
  - `imported` — Variables read but not defined within the chunk
  - `exported` — Variables defined within the chunk and used outside
  - `bound` — Variables bound by loop constructs
  - `dictionaries` — Dictionary access patterns
  - `arg_vars` — Build option variables referenced

A `FunctionSkeleton` is the typed function signature derived from `ChunkIO`:

- `args` / `pass_through_args` — Input parameters with mutability and type
- `maps` / `pass_through_maps` — Dictionary parameters
- `declared` — Local variable declarations
- `return_to_bind` / `return_to_overwrite` — Return values
- `bound_in_loop` — Loop-bound variables

### `Guard` / `Block` (`src/analyzer/guard.rs`)

Guards represent conditional execution contexts:

- **`Guard::N(negated, Atom)`** — A possibly-negated atomic condition
- **`Guard::And(Vec<Guard>)`** / **`Guard::Or(Vec<Guard>)`** — Boolean combinations
- **`Atom`** variants: `Var(name, VarCond)`, `Arg(name, VarCond)`, platform atoms (`Arch`, `Os`, `Cpu`, etc.), `PathExists`, `HasProgram`, `HasLibrary`, `HasHeader`, `Tautology`

A `Block` groups nodes under the same guard conditions and tracks its parent node.

### `Location` (`src/analyzer/location.rs`)

An execution-order-aware position in the script:

- **`node_id`** — The AST node
- **`exec_id`** — Global execution order
- **`order_in_expr`** — Position within a single expression
- **`line`** — Source line number

Locations are `Ord` and used for backward dataflow traversal and def-use chain construction.

## Data Flow

```
configure.ac
    |
    v
[autotools-parser: partial_expansion + Lexer + NodeParser]
    |
    v
AST (Slab<Node<AcCommand, NodeInfo>>)
    |
    +---> [GuardAnalyzer::analyze_blocks]     --> blocks with guards
    +---> [filter_out_commands]                --> remove irrelevant commands
    +---> [MacroFinder::find_macro_calls]      --> macro call index
    +---> [VariableAnalyzer::analyze_variables]--> per-node def/use/bind
    +---> [aggregate_def_use]                  --> global def-use maps + dependency edges
    +---> [run_value_set_analysis]             --> dynamic identifier resolution (VSA)
    +---> [run_type_inference]                 --> TypeHint -> DataType per variable
    +---> [make_dictionary_instances]          --> HashMap patterns from eval
    +---> [analyze_automake_files]             --> Makefile.am parsing
    +---> [run_build_option_analysis]          --> AC_ARG_ENABLE/WITH -> BuildOptionInfo
    +---> [consume_pkg_config_macros]          --> PKG_CHECK_MODULES -> PkgConfigAnalyzer
    +---> [create_conditional_compilation_map] --> CPP symbols -> cfg attributes
    +---> [flatten]                            --> large nested structures broken up
    +---> [construct_chunks]                   --> speculative lookahead chunking
    +---> [construct_chunk_skeletons]          --> typed function signatures
    |
    v
[run_extra_build_option_analysis]  (async, LLM)
    |
    v
[translate]  (async, LLM + rule-based)
    |
    v
[generate_cargo_toml + print_build_rs + generate_wrapper_header + print_conditional_compilation_map]
    |
    v
Cargo.toml + build.rs + wrapper.h + conditional_compilation_map.json
```

## Module Map

| Source file | Purpose |
|-------------|---------|
| `src/main.rs` | CLI entry point (clap), constructs `AnalyzerOptions`, calls `analysis()` |
| `src/analysis.rs` | Pipeline orchestration: creates `Analyzer`, runs LLM stages, writes output files |
| `src/display.rs` | `AutoconfPool` — AST pretty-printer, node display formatting |
| `src/utils.rs` | Utility functions (path helpers, extension checks) |
| `src/utils/glob.rs` | Shell glob pattern enumeration |
| `src/utils/enumerate.rs` | Cartesian product enumeration for value set combinations |
| `src/utils/llm_analysis.rs` | `LLMAnalysis` trait — generic interface for LLM-based analyses |
| `src/analyzer.rs` | Core types: `Analyzer`, `NodeInfo`, `AstVisitor`, `AnalyzerOptions`, `ProjectMetadata` |
| `src/analyzer/macro_call.rs` | `MacroFinder` visitor, `FixedMacroSideEffect` |
| `src/analyzer/macro_call/macros_list.rs` | 600+ M4 macro signature database |
| `src/analyzer/flatten.rs` | `Flattener` — breaks deeply nested structures above threshold |
| `src/analyzer/variable.rs` | `VariableAnalyzer` visitor, `Identifier`, `ValueExpr`, def-use tracking |
| `src/analyzer/value_set_analysis.rs` | Backward dataflow: resolves dynamic identifiers from `eval`, `VSACache` |
| `src/analyzer/type_inference.rs` | `TypeInferrer` visitor, `DataType`, `TypeHint`, hint-based inference |
| `src/analyzer/guard.rs` | `Guard`, `Atom`, `Block`, `GuardAnalyzer`, conditional context analysis |
| `src/analyzer/build_option.rs` | `BuildOption`, `BuildOptionInfo`, `CargoFeature`, option-to-feature mapping |
| `src/analyzer/build_option/use_llm.rs` | LLM-based value partitioning for build options |
| `src/analyzer/pkg_config.rs` | `PkgConfigAnalyzer`, system package manager trait, header discovery |
| `src/analyzer/automake.rs` | `AutomakeAnalyzer` — Makefile.am parsing, target/source/conditional extraction |
| `src/analyzer/platform_support.rs` | Platform detection variables and target triple mapping |
| `src/analyzer/dictionary.rs` | `DictionaryInstance`, `DictionaryAccess` — eval-driven HashMap patterns |
| `src/analyzer/project_info.rs` | `ProjectInfo` — source files, headers, config files, build artifacts |
| `src/analyzer/filtering.rs` | Removes commands irrelevant to build configuration |
| `src/analyzer/removal.rs` | Node removal from the AST pool |
| `src/analyzer/chunk.rs` | `Chunk`, `ChunkIO`, `FunctionSkeleton`, `Scope` — chunking algorithm |
| `src/analyzer/translator.rs` | Translation orchestration: inlined vs LLM, `TranslationResult`, code generation |
| `src/analyzer/translator/pretranslation.rs` | Rule-based macro-to-Rust translations (AC_CHECK_SIZEOF, AC_CHECK_TYPE, etc.) |
| `src/analyzer/translator/use_llm.rs` | LLM translation: prompt construction, validation layers, retry logic |
| `src/analyzer/translator/printer.rs` | `TranslatingPrinter` — AST-to-Rust-skeleton printer for LLM prompts |
| `src/analyzer/conditional_compilation.rs` | `ConditionalCompilationMap` — CPP symbol to `cfg` attribute mapping |
| `src/analyzer/record.rs` | `RecordCollector` — evaluation metrics (timing, costs, success rates, CSV/JSON export) |
| `src/analyzer/location.rs` | `Location`, `ExecId` — execution-order-aware positions |

## External Dependencies

- **`autotools-parser`** Forked `conch-parser` extended with M4 macro parsing. Provides AST types (`Node`, `AcCommand`, `M4Macro`, `M4Argument`), the `Lexer`, `NodeParser`, partial expansion, and the 600+ macro signature database.
- **`llm`** — LLM API client for build option analysis and chunk translation.
- **`slab`** — Arena allocator for AST nodes, blocks, and chunks.
- **`pkg-config`** — System library discovery at analysis time.
