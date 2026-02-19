---
name: simply-typed-lambda-calculus
description: 'Implements STLC with products, sums, and unit type. Use when: (1) Learning
  type systems, (2) Building interpreters, (3) Formalizing languages.'
version: 1.0.0
tags:
- type-systems
- lambda-calculus
- stlc
- foundations
difficulty: beginner
languages:
- python
- ocaml
- haskell
dependencies:
- lambda-calculus-interpreter
---

# Simply-Typed Lambda Calculus

Implements the simply-typed lambda calculus (STLC) with extensions.

## When to Use

- Learning type systems
- Building interpreters
- Formal verification
- Language prototyping

## What This Skill Does

1. **Implements base STLC** - Functions, variables
2. **Adds products** - Pairs, projections
3. **Adds sums** - Tagged unions
4. **Proves soundness** - Progress + preservation

## How to Use

1. Define syntax for types and terms
2. Implement typing judgment `Γ ⊢ e : τ`
3. Implement small-step evaluation
4. Prove progress and preservation for each reduction rule

## Key Concepts

| Concept | Description |
|---------|-------------|
| **Function type** | τ₁ → τ₂ (arrow) |
| **Product type** | τ₁ × τ₂ (pairs) |
| **Sum type** | τ₁ + τ₂ (tagged unions) |
| **Unit** | Terminal object |
| **Soundness** | Progress + Preservation |

## Extensions

| Extension | Description |
|-----------|-------------|
| **Polymorphism** | Type variables (System F) |
| **Recursion** | Fixed-point combinator |
| **References** | Mutable state |
| **Subtyping** | Width/depth subtyping |

## Tips

- Start with base STLC
- Add features one at a time
- Prove soundness incrementally
- Use de Bruijn indices for binding

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| **Barendregt, "The Lambda Calculus"** | Definitive reference on λ-calculus variants |
| **Pierce, "Types and Programming Languages", Ch. 5-9** | STLC with products, sums, recursive types |
| **Girard, Lafont, Taylor, "Proofs and Types"** | System F and type theory foundations |
| **Mitchell, "Foundations for Programming Languages"** | Comprehensive type systems coverage |

## Related Skills

- `lambda-calculus-interpreter` - Untyped lambda calculus
- `type-checker-generator` - Type checkers
- `dependent-type-implementer` - Dependent type theory

## Research Tools & Artifacts

Formalizations of STLC in proof assistants:

| Formalization | Proof Assistant | What to Learn |
|---------------|-----------------|---------------|
| **TAPL in Coq** | Coq | Full soundness proofs |
| **Software Foundations** | Coq | Pedagogical development |
| **Homotopy Type Theory** | Agda | Higher inductive types |
| **PFPL** | Coq | Pierce's formalization |

### Key Implementations

- **OCaml's type system** - Industrial STLC with extensions
- **GHC Core** - STLC with let-floating optimization
- **STLC in Lean** - Metaprogramming for type theory

## Research Frontiers

### 1. Normalization
- **Goal**: Prove that evaluation always terminates
- **Technique**: Logical relations, reducibility candidates
- **Papers**: Girard, Lafont & Taylor "Proofs and Types" (Chapter 4-6); Tait's method
- **Application**: Proof assistants, termination checking

### 2. Characterization of Terms
- **Goal**: What functions are definable in STLC?
- **Key result**: STLC terms are strongly normalizing (not Turing complete without recursion/fixpoint)
- **Paper**: "The Church-Rosser Property" (Curry & Feys)
- **Technique**: Reducibility candidates

### 3. Semantic Readback
- **Goal**: Reconstruct terms from normal forms
- **Technique**: Normalization by evaluation (NbE)
- **Papers**: "Normalization by Evaluation" (Berger & Schwichtenberg)
- **Application**: Reification, proof extraction

## Implementation Pitfalls

| Pitfall | Symptom | Solution |
|---------|---------|----------|
| **Missing arrow type case** | Unchecked function types crash | Handle TFun in all cases |
| **Wrong environment scoping** | Closures capture wrong values | Deep copy or escape analysis |
| **Substitution order** | Alpha renaming conflicts | Use de Bruijn indices |
| **Preservation proof gap** | Type changes after reduction | Prove lemma for each rule |

### The "Type Preservation is Non-Obvious" Lesson

Each evaluation rule needs a preservation proof:

```python
# For App: if ⊢ e1 : A→B and ⊢ e2 : A
#          and e1 e2 → e'[e2/x]
#          then ⊢ e'[e2/x] : B

# Need substitution lemma:
# If Γ, x:A ⊢ e : B and Γ ⊢ v : A
# then Γ ⊢ e[x↦v] : B
```

This is why STLC soundness takes effort to prove!
