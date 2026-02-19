---
name: lean-prover
description: A skill for using Lean 4, a modern interactive theorem prover with powerful type theory, dependent types, and mathematical structures.
version: "1.0.0"
tags: [lean, proof-assistant, theorem-proving, dependent-types, verification]
difficulty: advanced
languages: [lean]
dependencies: [dependent-type-implementer]
---

# Lean Prover

**Domain**: Proof Assistant / Formal Verification

## Overview

A skill for using Lean 4, a modern interactive theorem prover with powerful type theory, dependent types, and mathematical structures.

## Capabilities

- Define mathematical structures and theories
- Prove theorems interactively
- Build certified programs
- Create mathematical libraries
- Implement custom automation

## Key Concepts

- **Dependent Types**: Types depending on values
- **Lean's Type Theory**: Inductive types, structures, classes
- **Tactics**: Proof automation and construction
- **Monads**: State, IO, reader monads in proofs
- **Metaprogramming**: Custom proof automation

## Lean Features

- Extensible syntax and semantics
- Natural number game
- Mathematical library (mathlib)
- Continuous predicates
- Homotopy type theory support

## Use Cases

- Formal mathematics
- Program verification
- Compiler certification
- Language meta-theory
- Mechanized proofs

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| **Avigad, Massot, "Mathematics in Lean"** | Official Lean tutorial |
| **Carneiro, "The Type Theory of Lean" (2019)** | Lean's type theory foundation |
| **mathlib documentation** | Mathematical library examples |
| **Lean 4 manual** | Language reference |

## Research Tools & Artifacts

Lean ecosystem:

| Tool | What to Learn |
|------|---------------|
| **mathlib** | Mathematics library |
| **Lean 4** | Implementation |
| **Lean 3** | Previous version |
| **Verso** | Documentation tool |

## Research Frontiers

### 1. Metaprogramming
- **Goal**: Custom automation and tactics
- **Approach**: Lean 4 metaprogramming API
- **Papers**: "Metaprogramming in Lean 4" (2020)

### 2. Automation
- **Goal**: More powerful proof automation
- **Approach**: AI-assisted proving, auto-params
- **Papers**: "ProofNet" experiments

## Implementation Pitfalls

| Pitfall | Real Consequence | Solution |
|---------|-----------------|----------|
| **Proof complexity** | Large proofs | Structure with lemmas |
| **Universe issues** | Universe level errors | Explicit universe annotations |
| **Definitional vs propositional** | Wrong equality type | Use appropriate eq |
