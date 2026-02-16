# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

## [Unreleased]

### Added

- **Template**: Added `template/SKILL.md` as a reference template for new skills
- **CI Validation**: Added `.github/workflows/validate-skills.yml` for automated skill validation
- **Validation Script**: Added `scripts/validate_skills.py` to validate SKILL.md format and cross-references
- **Metadata Script**: Added `scripts/add_metadata.py` to standardize skill metadata
- **Reference Fix Script**: Added `scripts/fix_references.py` to fix broken cross-references
- **Pipelines**: Added `pipelines/` directory with example workflows
  - `compiler-pipeline.md`: End-to-end compiler building workflow
  - `verification-pipeline.md`: Program verification workflow
  - `type-system-pipeline.md`: Type system implementation workflow
- **Examples**: Added `examples/` directories with runnable test cases
  - `lambda-calculus-interpreter/examples/interpreter.py`
  - `type-checker-generator/examples/type_checker.py`
  - `abstract-interpretation-engine/examples/abstract_interpreter.py`
- **Enhanced Skill Manager**:
  - Tag-based filtering
  - Language-based filtering
  - Difficulty-based filtering
  - Dependency resolution and ordering
  - Dependency tree visualization
  - Improved search functionality
- **New Skills**: Added 19 new PL research skills (total now 87):
  - **Type Theory**: `system-f`, `gadt-implementer`, `type-class-implementer`, `existential-types`
  - **Compilation**: `register-allocator`, `dead-code-eliminator`, `loop-optimizer`, `inline-expander`
  - **Semantics**: `abstract-machine`, `axiomatic-semantics`, `reduction-semantics`
  - **Analysis**: `points-to-analysis`, `liveness-analysis`, `escape-analysis`, `shape-analysis`
  - **Verification**: `smt-solver-interface`, `dafny-verifier`, `concurrency-verifier`
  - **Runtime/Meta**: `memory-allocator`, `module-system`, `macro-expander`, `ffi-designer`
- **Extended Skills**: Added 7 more PL research skills (total now 94):
  - **Concurrency**: `lock-free-data-structure`, `message-passing-system`, `transactional-memory`
  - **Security**: `information-flow-analyzer`, `capability-system`, `sandbox-builder`
  - **Effects**: `effect-system`
- **New Skills**: Added 5 more PL research skills (total now 99):
  - **Effects**: `algebraic-effects`, `monad-transformer`
  - **Testing**: `property-based-tester`, `fuzzer-generator`
  - **Tooling**: `language-server-protocol`

### Changed

- **Metadata Standardization**: Added standardized frontmatter to all 66 skills:
  - `version`: Skill version (default: "1.0.0")
  - `tags`: Array of relevant tags
  - `difficulty`: beginner | intermediate | advanced
  - `languages`: Array of programming languages
  - `dependencies`: Array of related skill names
- **Fixed Cross-References**: Replaced 25+ broken references with valid alternatives:
  - `type-soundness-prover` → `hoare-logic-verifier`
  - `verified-compiler-builder` → `llvm-backend-generator`
  - `virtual-machine-designer` → `jit-compiler-builder`
  - And many more...
- **Fixed Missing Frontmatter**: Added proper frontmatter to 11 skills that were missing it:
  - `bidirectional-type-checking`
  - `contextual-equivalence`
  - `control-flow-analysis`
  - `incremental-computation`
  - `interprocedural-analysis`
  - `lean-prover`
  - `multi-stage-programming`
  - `polymorphic-effects`
  - `program-transformer`
  - `type-directed-name-resolution`
  - `value-analysis`

### Fixed

- Fixed 27 files with broken cross-references
- Fixed 11 files with missing or invalid frontmatter
- Updated skill manager backend with new API endpoints for tags, languages, and dependencies
- Updated skill manager frontend with improved filtering and dependency visualization

## [1.0.0] - Initial Release

### Added

- Initial collection of 51+ PL research skills
- Skills organized by conference track (POPL, PLDI, OOPSLA)
- Each skill contains:
  - Detailed documentation
  - Code examples
  - Canonical references
  - Tradeoffs and limitations
  - Assessment criteria
- Skills Manager web interface
- Contributing guidelines
- README in English and Chinese
