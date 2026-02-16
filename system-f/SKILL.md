---
name: system-f
description: "Implement System F (polymorphic lambda calculus) with type abstraction and application."
version: "1.0.0"
tags: [type-theory, polymorphism, lambda-calculus, popl]
difficulty: advanced
languages: [haskell, ocaml, python]
dependencies: [simply-typed-lambda-calculus, type-inference-engine]
---

# System F (Polymorphic Lambda Calculus)

System F, also known as the polymorphic lambda calculus or Girard-Reynolds calculus, extends the simply-typed lambda calculus with type abstraction and type application, enabling universal quantification over types.

## When to Use This Skill

- Implementing polymorphic type systems
- Building generic programming constructs
- Researching type theory foundations
- Implementing ML-style module systems
- Understanding parametric polymorphism

## What This Skill Does

1. **Type Abstraction (Λ)**: Bind type variables in terms, written as `Λα. t`
2. **Type Application**: Instantiate polymorphic terms with concrete types, written as `t [T]`
3. **Universal Types**: Express types like `∀α. τ` for polymorphic values
4. **Kind System**: Handle type-level computation and classification
5. **Type Safety**: Prove progress and preservation theorems

## Key Concepts

| Concept | Description |
|---------|-------------|
| Type Abstraction | `Λα.t` binds type variable α in term t |
| Type Application | `t [T]` instantiates polymorphic term with type T |
| Universal Quantification | `∀α.τ` represents polymorphic types |
| Parametricity | Polymorphic functions behave uniformly across types |
| Predicativity | Type variables range only over "small" types |

## Tips

- Use De Bruijn indices for type variables to avoid capture
- Implement type substitution carefully to avoid variable capture
- Consider adding kind checking for higher-rank types
- Test with Church encodings to verify polymorphism
- Use bidirectional type checking for better error messages

## Common Use Cases

- Implementing generic data structures (lists, trees, maps)
- Building type-safe container libraries
- Researching type inference algorithms
- Understanding ML-style let-polymorphism
- Formalizing parametricity theorems

## Related Skills

- `simply-typed-lambda-calculus` - Foundation before System F
- `type-inference-engine` - Algorithm W for Hindley-Milner
- `type-class-implementer` - Type classes as alternative to System F
- `existential-types` - Dual to universal types

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| Girard, Lafont, Taylor (1989) "Proofs and Types" | Original System F presentation |
| Pierce "Types and Programming Languages" Ch. 23-24 | Modern textbook treatment |
| Reynolds "Types, Abstraction and Parametricity" | Parametricity theorem |

## Tradeoffs and Limitations

### Approach Tradeoffs

| Approach | Pros | Cons |
|----------|------|------|
| Explicit type abstraction | Simple, predictable | Verbose syntax |
| Type inference (HM) | Concise code | Less expressive than full System F |
| Bidirectional checking | Good error messages | Requires annotations at boundaries |

### When NOT to Use This Skill

- When Hindley-Milner type inference suffices (use `type-inference-engine`)
- For simple monomorphic programs (use `simply-typed-lambda-calculus`)
- When performance is critical (type erasure complicates optimization)

### Limitations

- Type reconstruction is undecidable for full System F
- Rank-N types require explicit annotations
- No built-in recursion (must add fixpoint combinator)

## Assessment Criteria

A high-quality implementation should have:

| Criterion | What to Look For |
|-----------|------------------|
| Type Safety | Proven progress and preservation |
| Substitution | Capture-avoiding type substitution |
| Error Messages | Clear indication of type mismatches |
| Parametricity | Polymorphic functions behave uniformly |

### Quality Indicators

✅ **Good**: Implements full System F with type abstraction/application, proven type safety
⚠️ **Warning**: Only handles rank-1 types, missing explicit type application
❌ **Bad**: No type abstraction, just simply-typed lambda calculus

## Research Tools & Artifacts

System F implementations:

| Tool | What to Learn |
|------|---------------|
| **GHC Core** | System F in practice |
| **Twelf** | Logical framework |

## Research Frontiers

### 1. Higher-Rank Types
- **Approach**: Rank-N polymorphism

## Implementation Pitfalls

| Pitfall | Real Consequence | Solution |
|---------|-----------------|----------|
| **Type inference** | Undecidable | Bidirectional |
