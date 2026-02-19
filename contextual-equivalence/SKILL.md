---
name: contextual-equivalence
description: A skill for proving contextual equivalence between programs using operational semantics, bisimulation, and related techniques.
version: "1.0.0"
tags: [verification, equivalence, bisimulation, operational-semantics]
difficulty: advanced
languages: [ocaml, coq]
dependencies: [operational-semantics-definer, bisimulation-checker]
---

# Contextual Equivalence

**Domain**: Program Verification / Programming Languages

## Overview

A skill for proving contextual equivalence between programs using operational semantics, bisimulation, and related techniques.

## Capabilities

- Prove that two programs are contextually equivalent
- Build bisimulation relations for behavioral equivalence
- Use operational semantics to reason about program behavior
- Apply contextual equivalence in compiler verification

## Techniques

- **Operational Semantics**: Small-step and big-step semantics
- **Bisimulation**: Trace equivalence, bisimilarity proofs
- **Contextual Equivalence**: Observation-based equivalence
- **Game Semantics**: Interactive models of computation

## Use Cases

- Compiler correctness proofs
- Program transformation verification
- Optimization validation
- Language meta-theory development

## References

| Reference | Why It Matters |
|-----------|----------------|
| **Morris, "Lambda Calculus Types and Models" (1968)** | Original contextual equivalence formulation |
| **Milner, "Operational and Algebraic Semantics" (1997)** | Comprehensive overview of contextual equivalence |
| **Gunter, "Semantic Foundations for Programming Languages"** | Formal treatment of program equivalence |
| **Reynolds, "Theories of Programming Languages"** | Contextual equivalence in type theory |

See also: `../simply-typed-lambda-calculus`, `../bisimulation-checker`, `../operational-semantics-definer`

## Research Tools & Artifacts

Real-world contextual equivalence verification:

| Tool | Why It Matters |
|------|----------------|
| **Coq** | Interactive proof of contextual equivalence |
| **Twelf** | Logical framework for LF |
| **Agda** | Dependent types for equivalence proofs |
| **Nuprl** | Constructive verification system |
| **HOL** | Higher-order logic proofs |

### Key Verification Projects

- **CompCert**: Verified compiler with contextual equivalence
- **GHC correctness**: Haskell compiler verification
- **CakeML**: Verified ML compiler

## Research Frontiers

Current contextual equivalence research:

| Direction | Key Papers | Challenge |
|-----------|------------|-----------|
| **Untyped equivalence** | "Equivalence in untyped λ-calculus" | Full abstraction |
| **Relational** | "Relational Reasoning" (2008) | Semantic relations |
| **Step-indexed** | "Step-indexed Bisimulation" (2005) | Recursive types |
| **Logical relations** | "Logical Relations" (1998) | Semantics |
| **Game semantics** | "Game Semantics" (1997) | Full abstraction |

### Hot Topics

1. **Probabilistic equivalence**: Contextual equivalence for probabilistic programs
2. **Differential privacy**: Verifying privacy via equivalence
3. **Quantum equivalence**: Quantum program equivalence

## Implementation Pitfalls

Common equivalence proof bugs:

| Pitfall | Real Example | Prevention |
|---------|--------------|------------|
| **Incomplete contexts** | Missing context forms | Prove completeness |
| **Bisimulation too strong** | Fails for equivalent programs | Use weak bisimulation |
| **Recursive types** | Fixed-point handling | Use step-indexing |
| **Non-termination** | Divergence not handled | Use contextual equivalence |
| **State** | State in language | Relational reasoning |
