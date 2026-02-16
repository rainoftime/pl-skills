---
name: program-transformer
description: A skill for transforming programs through various semantics-preserving and optimization passes.
version: "1.0.0"
tags: [transformation, optimization, compiler, refactoring]
difficulty: intermediate
languages: [haskell, ocaml, python]
dependencies: [cps-transformer, closure-converter]
---

# Program Transformer

**Domain**: Program Analysis / Compiler Engineering

## Overview

A skill for transforming programs through various semantics-preserving and optimization passes.

## Capabilities

- Implement source-to-source transformations
- Apply semantics-preserving optimizations
- Build program simplifiers
- Handle complex control flow
- Preserve program properties

## Transformation Types

- **Desugaring**: Remove syntactic sugar
- **Normalization**: Put programs in canonical form
- **Optimization**: Improve performance/space
- **Parallelization**: Detect parallel opportunities
- **Specialization**: Partial evaluation, specialization

## Techniques

- **AST Manipulation**: Tree transformations
- **Traversal Strategies**: Top-down, bottom-up, visitor patterns
- **Binding Management**: Alpha conversion, capture-avoiding substitution
- **Type-Preserving Transformations**: Type-safe rewrites

## Use Cases

- Compiler frontends/backends
- Program optimization
- Refactoring tools
- DSL implementation

## References

See: `../cps-transformer`, `../defunctionalization`, `../closure-converter`, `../common-subexpression-eliminator`

## Research Tools & Artifacts

Real-world program transformation tools:

| Tool | Why It Matters |
|------|----------------|
| **Rascal** | Program transformation |
| **Stratego** | Transformation language |
| **XSLT** | XML transformation |
| **K toolkit** | Rewriting framework |

### Key Systems

- **StrategoXT**: Transformation tool
- **Rascal**: Source code analysis

## Research Frontiers

Current transformation research:

| Direction | Key Papers | Challenge |
|-----------|------------|-----------|
| **Correctness** | "Verified Transformations" | Soundness |
| **Automation** | "Auto-transformation" | Discovery |

### Hot Topics

1. **ML transformation**: Learning transformations
2. **Wasm transformation**: Binary transforms

## Implementation Pitfalls

Common transformation bugs:

| Pitfall | Real Example | Prevention |
|---------|--------------|------------|
| **Preservation** | Wrong semantics | Prove |
