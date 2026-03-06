# c2cargo

Autotools-to-Cargo migration for C-to-Rust project-level translation.

## The Problem

Existing C-to-Rust transpilers (c2rust, etc.) translate individual source files but ignore the build system entirely. This loses conditional compilation logic, platform-specific configurations, library dependencies, and build options — all of which are encoded in autoconf/automake scripts (`configure.ac`, `Makefile.am`). Without migrating the build system, the resulting Rust project cannot compile or reproduce the original build behavior.

## What c2cargo Does

c2cargo analyzes autoconf/automake build scripts and generates equivalent Cargo build artifacts through a four-phase pipeline:

1. **Normalization & Parsing** — Expands M4 macros via a 600+ macro signature database, parses the script into an AST, and flattens deeply nested structures.
2. **Semantic Analysis** — Performs variable def-use analysis, value set analysis for dynamic identifiers, type inference, guard (conditional branch) analysis, build option mapping, and external dependency resolution.
3. **Fragment Decomposition & Translation** — Decomposes the script into small, dependency-aware chunks, then translates each fragment using rule-based pretranslation or LLM-assisted translation with multi-layer validation.
4. **Cargo Artifact Generation** — Produces `Cargo.toml`, `build.rs`, `wrapper.h`, and a conditional compilation map.

## Key Capabilities

- **600+ M4 macro signature database** with argument types and side-effect annotations
- **Set-based value analysis** for resolving dynamic identifiers from `eval` statements (handles for-loop enumeration, command substitution, Cartesian products)
- **Type inference** from shell variables to Rust types (Boolean, Integer, List, Path, Optional, Literal, Either)
- **Build option abstraction**: `./configure` flags (`--enable-*`, `--with-*`) mapped to Cargo features via LLM-assisted value partitioning with validation rules
- **Conditional compilation mapping**: C preprocessor symbols mapped to `#[cfg(...)]` attributes
- **External dependency resolution**: `PKG_CHECK_MODULES` mapped to `pkg-config` crate calls, with header discovery via system package managers
- **Fragment decomposition**: speculative lookahead windowing produces chunks that are 96-100% 1-5 lines
- **Hybrid translation**: rule-based pretranslation for known patterns + LLM translation with skeleton-guided prompting, syntax validation via `cargo check`, snippet preservation, and pattern rejection

## Getting Started

### Prerequisites

- Rust toolchain (stable)
- `autotools-parser` crate at `../autotools-parser` (see `Cargo.toml`)
- Optionally: `pkg-config` and `apt-file` (for external dependency resolution on Debian/Ubuntu)

### Build

```bash
cargo build --release
```

### Usage

```bash
c2cargo <path/to/configure.ac> [options]
```

### CLI Options

| Option | Default | Description |
|--------|---------|-------------|
| `<configure.ac>` | (required) | Path to the `configure.ac` file to analyze |
| `-o, --output-dir <DIR>` | `/tmp/c2cargo` | Output directory for generated files |
| `--full-script` | off | Use full-script translation mode (no chunking) |
| `--no-type-inference` | off | Disable type inference |
| `--chunk-window-size <N>` | `2` | Speculative lookahead window size for chunk fusing |
| `--flatten-threshold <N>` | `200` | Node count threshold for flattening nested structures |

## Generated Output

c2cargo produces the following artifacts in `<output-dir>/<project>-rs/`:

| File | Description |
|------|-------------|
| `Cargo.toml` | Package metadata from `AC_INIT`, features from build options, build dependencies |
| `build.rs` | Configuration logic: env var imports, translated fragments as Rust functions, `cfg`/`env` exports, bindgen setup |
| `wrapper.h` | Aggregated external library headers for bindgen (when `PKG_CHECK_MODULES` is used) |
| `record/conditinal_compilation_map.json` | C preprocessor symbols mapped to Rust `cfg` attributes |
| `record/project_info.json` | Project structure: source files, headers, automake files, build artifacts |
| `record/chunks.csv` | Per-chunk translation metrics (type, success, cost, duration) |
| `record/build_options.csv` | Per-option analysis metrics |

## Evaluation

Tested on GMP, libxml2, libpng, and HarfBuzz:
- 100% compilation success (top-k candidates)
- 62-94% build artifact preservation across projects

## Documentation

- [Architecture](doc/architecture.md) — System design, core abstractions, data flow
- [Pipeline](doc/pipeline.md) — Detailed walkthrough of each analysis phase
- [Modules](doc/modules.md) — Module reference grouped by pipeline phase

## License

MIT License. See [LICENSE](LICENSE).
