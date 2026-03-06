# Pipeline

Detailed walkthrough of c2cargo's four-phase pipeline. For a high-level overview and module map, see [architecture.md](architecture.md).

## Phase 1 — Normalization and Parsing

**Goal:** Transform raw `configure.ac` into a flat, analyzable AST.

### M4 Macro Expansion

The `autotools-parser` crate performs partial expansion of M4 macros:

```
autotools_parser::preprocess::partial_expansion(path, true)
```

This expands `m4_include`, `m4_sinclude`, and similar directives, inlining referenced `.m4` files. Autoconf macros (AC_*, AM_*, etc.) are preserved as structured `M4Macro` nodes in the AST rather than being expanded.

### Macro Signature Database

`src/analyzer/macro_call/macros_list.rs` contains a database of 600+ M4 macro signatures, specifying:

- **Argument types**: literal, word, command body, program text, array
- **Side effects**: which shell variables are defined or used, which CPP symbols are set
- **Variable attributes**: read, write, substituted

This database enables the analyzer to understand macro behavior without executing them.

### AST Construction

The `Lexer` and `NodeParser` produce a `Slab<Node<AcCommand, NodeInfo>>` — an arena of AST nodes where each node represents a shell command, assignment, control flow construct, or M4 macro invocation. Each node is assigned a `NodeId` (its slab index).

### Guard Analysis

`GuardAnalyzer::analyze_blocks()` walks the AST to build `Block` structures that track which conditional branch each node belongs to. Each block records its `guards` — the chain of conditions (if/case/test) that must hold for the block's commands to execute.

### Command Filtering

`filter_out_commands()` removes commands that don't affect build configuration (e.g., `echo` for user messages, `AC_MSG_*` macros, etc.).

### Flattening

`Flattener::flatten()` breaks deeply nested command structures (if/case blocks with more than `flatten_threshold` nodes) into top-level commands. This prevents overly large chunks and improves translation quality. The threshold defaults to 200 and is configurable via `--flatten-threshold`.

## Phase 2 — Semantic Analysis

**Goal:** Understand variable flow, types, conditions, and build semantics.

### Variable Def-Use Analysis (`src/analyzer/variable.rs`)

`VariableAnalyzer` walks the AST and records for each node:

- **Definitions**: variables assigned (`x=value`, `for x in ...`, M4 macro side effects)
- **Usages**: variables read (`$x`, `${x}`, in conditions, in macro arguments)
- **Bounds**: variables bound by for-loop constructs
- **Propagated definitions**: variables defined across all branches of a conditional (guaranteed initialization regardless of branch taken)
- **Eval assignments**: `eval` statements where the LHS variable name is dynamically constructed

`aggregate_def_use()` then builds global variable maps and computes dependency edges between nodes: if node B uses variable `x` and node A is the dominant definition of `x` before B, an edge A→B is created.

### Value Set Analysis (`src/analyzer/value_set_analysis.rs`)

Handles the hard case of `eval` statements where variable names are dynamically constructed:

```bash
eval "${prefix}_${suffix}=value"
```

The analyzer performs **backward dataflow** to resolve possible values:

1. **Chain construction**: For each `eval` assignment, traces backward through definitions to find all possible values of each variable component
2. **Value expression resolution**: Handles literals, variable references, concatenation, dynamic names (`DynName`), and command substitution (`Shell`)
3. **Cartesian product enumeration**: When multiple components have multiple possible values, enumerates all combinations
4. **Identifier division recording**: Maps dynamic identifiers back to their component variables with value mappings

Results are cached to disk (`/tmp/vsa_cache.*.bin`) keyed by a hash of the script path.

### Type Inference (`src/analyzer/type_inference.rs`)

`TypeInferrer` collects `TypeHint` values from usage patterns:

| Pattern | Hint |
|---------|------|
| Assigned `"yes"`, `"no"`, `"1"`, `"0"` | `CanBeBoolLike` |
| Assigned numeric string | `CanBeNum` |
| Assigned value with whitespace | `CanContainWhitespace` |
| Appears in `for var in $list` | `Iterated` + `UsedInFor(child)` |
| Self-referencing append (`"$var more"`) | `AppendedSelf` |
| Used as command name | `UsedAsCommand` |
| Used in redirection / `rm` / `cat` | `UsedAsPath` |
| Used in `expr` or arithmetic | `Calculated` |
| Compared with `-ge`, `-lt`, etc. | `SizeComparison` |

Hints are resolved to `DataType`:

- `Boolean` — `bool`
- `Integer` — `usize`
- `List(T)` — `Vec<T>`
- `Path` — `PathBuf`
- `Optional(T)` — `Option<T>`
- `Literal` — `String` (default)
- `Either(T, values)` — `String` (with known value set)

A known-types table provides pre-assigned types for standard autoconf variables (`CC`, `CFLAGS`, `LIBS`, `prefix`, `srcdir`, etc.).

### Guard Analysis (`src/analyzer/guard.rs`)

Guards model conditional execution contexts. The `GuardAnalyzer` extracts conditions from:

- `if` / `elif` / `else` branches
- `case` arms
- `test` commands
- `&&` / `||` chains

Guard atoms include:

- `Var(name, VarCond)` / `Arg(name, VarCond)` — Variable/argument equality, emptiness, match patterns
- Platform atoms: `Arch`, `Os`, `Cpu`, `Env`, `Abi`, `ArchGlob`, `OsAbiGlob`
- `PathExists`, `HasProgram`, `HasLibrary`, `HasHeader`
- `Compiler(name)` — Compiler detection
- `Tautology` — Always true/false

Guards are used for:
1. Determining dominant definitions (only definitions under compatible guards count)
2. Conditional compilation mapping
3. Build option guard conversion

### Build Option Analysis (`src/analyzer/build_option.rs`)

Extracts `AC_ARG_ENABLE` and `AC_ARG_WITH` macro calls:

1. **Extraction**: Identifies option names and associated variables
2. **Guard conversion**: Reclassifies variable guards as argument guards (`Atom::Var` → `Atom::Arg`)
3. **Value candidate collection**: Gathers all literal values compared against option variables
4. **Context collection**: Follows variable flow to find related commands
5. **LLM-assisted partitioning** (`build_option/use_llm.rs`): For each option, the LLM determines representative values, aliases, and default state
6. **Cargo feature construction**: Maps partitioned values to Cargo features (boolean options → single feature, enum options → one feature per representative)

Results are cached to disk (`/tmp/build_option_cache.*.bin`).

### External Dependency Resolution (`src/analyzer/pkg_config.rs`)

Processes `PKG_CHECK_MODULES` macro calls:

1. Extracts package names from macro arguments
2. Queries `pkg-config` for `.pc` file locations
3. Uses system package managers (`apt-file` on Debian/Ubuntu) to discover header files
4. Maps packages to variables (`PKG_CFLAGS`, `PKG_LIBS`)
5. Generates `pkg-config` crate calls for `build.rs`

### Automake Analysis (`src/analyzer/automake.rs`)

Parses `Makefile.am` files to extract:

- Source file lists (`*_SOURCES`, `EXTRA_*_SOURCES`)
- Build targets and their types (programs, libraries, headers)
- Automake conditionals and their mapping to autoconf variables
- Link dependencies (`*_LDADD`, `*_LIBADD`)
- Compiler flags (`*_CFLAGS`, `*_LDFLAGS`)

### Dictionary Instances (`src/analyzer/dictionary.rs`)

When value set analysis discovers that `eval` creates families of variables with a common structure (e.g., `${prefix}_${key}=value`), the analyzer creates `DictionaryInstance` objects — these represent `HashMap` patterns where dynamic variable indexing becomes keyed map access in Rust.

### Conditional Compilation Map (`src/analyzer/conditional_compilation.rs`)

Scans `config.h.in` and similar template files to map:

- C preprocessor `#define` / `#undef` symbols to Rust `cfg` attributes
- `AC_SUBST` variables used in `#if` / `#ifdef` guards
- Automake conditionals controlling source file inclusion

Produces a JSON map consumed by the generated `build.rs`.

## Phase 3 — Fragment Decomposition and Translation

**Goal:** Decompose the script into translatable fragments and convert them to Rust.

### Chunk Decomposition (`src/analyzer/chunk.rs`)

The `construct_chunks()` algorithm:

1. Iterates through top-level nodes in execution order
2. **Dependency check**: If the next node shares a def-use relationship with the current chunk, fuse them
3. **Speculative lookahead**: If no direct relationship, look ahead up to `chunk_window_size` nodes (default: 2) to find transitive relationships
4. **Assignment skipping**: Optionally, assignment-only nodes don't consume window depth
5. **Boundary enforcement**: Flattened nodes always start a new chunk
6. **I/O examination**: For each chunk, compute imported/exported variables, dictionary accesses, and build option references

This produces chunks where 96-100% contain 1-5 nodes.

After chunking, `cut_variable_scopes_chunkwise()` determines variable scope boundaries — which chunks own, read, or overwrite each variable — and `construct_chunk_skeletons()` builds typed function signatures (`FunctionSkeleton`) from the scope information.

### Pretranslation (`src/analyzer/translator/pretranslation.rs`)

Known macro patterns are directly translated without LLM involvement:

- `AC_CHECK_SIZEOF` → `check_sizeof()` call
- `AC_CHECK_TYPE` / `AC_CHECK_TYPES` → `check_type()` call
- `AC_INIT` → project metadata extraction
- `AM_INIT_AUTOMAKE` → automake initialization

### Inlined Translation (`src/analyzer/translator.rs`)

Simple chunks (single assignments, trivial commands) are translated inline:

- Literal assignments → typed Rust assignments based on `DataType`
- Self-referencing appends → `.push()` / `.push_str()` based on inferred type
- Single-node chunks without exports → inline code insertion

### LLM Translation (`src/analyzer/translator/use_llm.rs`)

For complex chunks:

1. **Skeleton construction**: The `TranslatingPrinter` converts AST nodes into a Rust-like pseudo-code representation, replacing M4 macros with equivalent Rust function calls
2. **Prompt assembly**: The skeleton (function signature + header + body placeholder + footer) is provided to the LLM along with predefined helper function signatures
3. **Validation layers** (applied to each LLM response):
   - Syntax check via `cargo check` on a temporary crate
   - Required snippet preservation (specific strings that must appear)
   - Literal validation (known values must be present)
   - Pattern rejection (banned patterns that indicate hallucination)
   - Extra validation functions (e.g., excessive backslash detection)
4. **Retry**: Up to 10 attempts with validation feedback

### TranslatingPrinter (`src/analyzer/translator/printer.rs`)

Converts AST nodes to Rust-like code for LLM prompts:

- Shell assignments → Rust variable assignments with type-appropriate formatting
- `if`/`case`/`for` → Rust control flow
- M4 macros → predefined Rust function calls (e.g., `AC_CHECK_HEADER` → `check_header()`)
- Guard conditions → Rust boolean expressions with `cfg!()` for platform checks
- Dictionary accesses → `HashMap` operations
- Build option references → `cfg!(feature = "...")` checks

## Phase 4 — Cargo Artifact Generation

**Goal:** Produce the final Rust build system artifacts.

### Cargo.toml (`Analyzer::generate_cargo_toml`)

Generated from:
- `AC_INIT` metadata → `[package]` (name, version, homepage)
- Build option analysis → `[features]` with defaults and dependencies
- Fixed build dependencies: `regex`, `pkg-config`, `bindgen`

### build.rs (`Analyzer::print_build_rs`)

Structured as:

```rust
// predefinition — helper functions (check_header, check_library, pkg_config, etc.)

fn main() {
    // import environmental variables (option_env! for CC, CFLAGS, etc.)
    // default variable initialization
    // translated fragments (function calls to chunk functions)
    // export cfg/env via AC_SUBST
    // export cfg for automake conditionals
    // bindgen setup
    // record subst vars for evaluation
}

// chunk functions — one per translated chunk
```

The output is formatted via `rust-format` (`RustFmt`).

### wrapper.h

When `PKG_CHECK_MODULES` calls are present, aggregates all discovered external library headers into a single `wrapper.h` for bindgen.

### Conditional Compilation Map

Serialized as JSON mapping C preprocessor symbols to Rust `cfg` attributes, with migration type (`Cfg`, `Env`, `Fixed`, `Set`, `Unset`).

### Evaluation Records (`src/analyzer/record.rs`)

`RecordCollector` exports:

- `project_info.json` — Source files, headers, automake files, commands, chunks
- `build_options.csv` — Per-option: success, cost, duration, features generated
- `chunks.csv` — Per-chunk: translation type, success, cost, duration, retries
- `record.csv` — Runtime recording of `AC_SUBST` variable values for evaluation
