---
name: gadt-implementer
description: "Implement Generalized Algebraic Data Types (GADTs) for expressive type-safe data structures."
version: "1.0.0"
tags: [type-theory, data-structures, haskell, pldi]
difficulty: advanced
languages: [haskell, ocaml, rust]
dependencies: [type-checker-generator, simply-typed-lambda-calculus]
---

# GADT Implementer

Generalized Algebraic Data Types (GADTs) extend ordinary algebraic data types by allowing constructors to have different return types, enabling more precise type indexing and type-safe encodings.

## When to Use This Skill

- Implementing typed abstract syntax trees (ASTs)
- Building type-safe embedded domain-specific languages
- Creating phantom-typed data structures
- Implementing well-typed interpreters
- Encoding invariants in types

## What This Skill Does

1. **GADT Declaration**: Define data types where constructors return different type indices
2. **Type Indexing**: Use type parameters to track additional information
3. **Pattern Matching with Type Refinement**: Refine types in pattern branches
4. **Existential Quantification**: Hide type parameters in constructors
5. **Type-Level Programming**: Encode properties in the type system

## Key Concepts

| Concept | Description |
|---------|-------------|
| Type Index | Type parameter that tracks additional information |
| Type Refinement | Pattern matching reveals more specific types |
| Existential | Constructors can hide type arguments |
| Phantom Types | Type parameters with no runtime representation |
| Type Witnesses | Values that witness type equalities |

## Tips

- Use `{-# LANGUAGE GADTs #-}` or `{-# LANGUAGE GADTSyntax #-}` in GHC
- Combine with `DataKinds` for type-level programming
- Use `TypeApplications` for disambiguation
- Pattern matching provides type equalities - use them!
- Consider using `ExistentialQuantification` with GADTs

## Common Use Cases

- Implementing typed ASTs for compilers and interpreters
- Building type-safe protocol implementations
- Creating well-typed generic traversals
- Encoding state machines in types
- Implementing finally tagless interpreters

## Related Skills

- `type-checker-generator` - Type checking for GADTs
- `dependent-type-implementer` - More expressive than GADTs
- `existential-types` - Existential quantification
- `simply-typed-lambda-calculus` - Foundation for typed ASTs

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| **Xi, Chen & Chen, "Guarded Recursive Datatype Constructors" (POPL 2003)** | Original paper introducing GADTs in ML/Haskell |
| **Peyton Jones, Vytiniotis, Weirich & Shields, "Practical Type Inference for Arbitrary-Rank Types" (JFP 2007)** | Type inference for GADTs and rank-N polymorphism |
| GHC User's Guide "GADTs" | Practical implementation details |

## Tradeoffs and Limitations

### Approach Tradeoffs

| Approach | Pros | Cons |
|----------|------|------|
| GADTs | Precise types, no runtime checks | Complex type errors |
| Phantom types | Simpler | Less expressive |
| Finally tagless | No GADT syntax needed | Different style |

### When NOT to Use This Skill

- When simple algebraic data types suffice
- For performance-critical code (extra indirection)
- When type error messages are critical for users

### Limitations

- Type inference is less complete than for normal ADTs
- Cannot use deriving clauses for all type classes
- Pattern matching must be complete for type safety

## Assessment Criteria

A high-quality implementation should have:

| Criterion | What to Look For |
|-----------|------------------|
| Type Safety | Pattern matching refines types correctly |
| Completeness | Handles all GADT features (existentials, equality) |
| Error Messages | Clear indication of type mismatches |
| Inference | Infers types where possible |

### Quality Indicators

✅ **Good**: Type-safe evaluator with no runtime checks, clear GADT structure
⚠️ **Warning**: Overuses GADTs when simpler types would work
❌ **Bad**: GADT structure doesn't actually provide type safety benefits

## Research Tools & Artifacts

GADT implementations:

| Tool | Language | What to Learn |
|------|----------|---------------|
| **GHC** | Haskell | Production GADTs |
| **OCaml** | OCaml | GADTs |
| **Rust** | Rust | GADTs |

## Research Frontiers

### 1. Dependent Types
- **Approach**: GADTs as mini dependent types

## Implementation Pitfalls

| Pitfall | Real Consequence | Solution |
|---------|-----------------|----------|
| **Type errors** | Confusing errors | Better error messages |
