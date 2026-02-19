---
name: dependent-type-implementer
description: 'Implements dependently typed lambda calculus (Pi types). Use when: (1)
  Building proof assistants, (2) Formalizing mathematics, (3) Verified programming.'
version: 1.0.0
tags:
- type-systems
- dependent-types
- type-theory
- proofs
difficulty: advanced
languages:
- python
- agda
- idris
dependencies:
- simply-typed-lambda-calculus
---

# Dependent Type Implementer

Implements dependent type theory (Type Theory, Π Types, Σ Types).

## When to Use

- Building proof assistants (Coq, Agda, Idris)
- Formalizing mathematics
- Verified programming
- Type-level computation

## What This Skill Does

1. **Implements Π types** - Dependent functions τ → σ(x)
2. **Implements Σ types** - Dependent pairs (x:τ) × σ(x)
3. **Type checking** - With conversion and unification
4. **Proof elaboration** - From surface to core syntax

## How to Use

1. Start from a minimal core (`Var`, `Pi`, `Lam`, `App`, universes)
2. Implement normalization and definitional equality
3. Type-check by synthesis/checking with conversion
4. Add `Sigma`, naturals, and eliminators incrementally

## Core Theory

```
Dependent Function (Π):
  Π(x:A). B  or  (x:A) → B
  
  When x not in B: A → B (non-dependent)

Dependent Pair (Σ):
  Σ(x:A). B  or  (x:A) × B
  
  When x not in B: A × B (product)

Type formation rules:
  Γ ⊢ A : s    Γ, x:A ⊢ B : s
  ------------------------------
  Γ ⊢ Π(x:A).B : s
  
  Γ ⊢ A : s    Γ, x:A ⊢ B : s
  ------------------------------
  Γ ⊢ Σ(x:A).B : s
```

## Implementation

```
(* Core Syntax (conceptual) *)

Term types:
  - Type (universe)
  - Var (de Bruijn index)
  - Lam (abstraction with optional type annotation)
  - App (application)
  - Pi (dependent function type)
  - Sigma (dependent pair type)
  - Pair, Proj1, Proj2 (pair intro/elim)
  - Unit, Nat, Zero, Succ, NatElim (basic types)

Type formation rules:
  Γ ⊢ A : s    Γ, x:A ⊢ B : s
  ------------------------------
  Γ ⊢ Π(x:A).B : s

  Γ ⊢ A : s    Γ, x:A ⊢ B : s
  ------------------------------
  Γ ⊢ Σ(x:A).B : s

Typing rules (key cases):
  T_Abs:  Γ ⊢ A : s
          Γ, x:A ⊢ N : B
          ----------------
          Γ ⊢ λx:A. N : Π(x:A).B

  T_App:  Γ ⊢ M : Π(x:A).B
          Γ ⊢ N : A
          -----------------
          Γ ⊢ M N : B[x := N]

  T_Pair: Γ ⊢ M : A
          Γ ⊢ N : B[x := M]
          ------------------
          Γ ⊢ (M, N) : Σ(x:A).B
```

## Elaboration

```
From surface syntax to core:

Surface: λ(x : A) => e
Core:    Lam A e

Elaboration algorithm:
1. Infer type of binding: A : s
2. Extend context with x : A
3. Elaborate body: e : B
4. Compute result type:
   - Non-dependent: Pi A (λx. B)
   - Dependent: Pi A (λx. B)

Pattern matching elaboration:
  match e return P with
  | c1 => e1
  | c2 => e2
  end

  becomes:
  NatElim P e (λ_. e1) (λn. λIH. e2)
```

## Universe Polymorphism

```coq
(* Cumulative universes *)
Inductive universe : Type :=
  | Set0 : universe
  | Set1 : universe
  | Set2 : universe
  | ... (* Prop, SProp, etc. *)

(* Universe constraints *)
Check (Type@{i} -> Type@{j}).
(* i ≤ j required *)

(* Cumulative: Set@{i} ≤ Set@{i+1} *)
```

## Implementation in OCaml

```ocaml
(* Core dependent type checker *)

type term =
  | Var of int
  | Lambda of term * term
  | App of term * term
  | Pi of term * term        (* Π x : A. B *)
  | Sigma of term * term     (* Σ x : A. B *)
  | Pair of term * term
  | Proj1 of term
  | Proj2 of term
  | Star                       (* unit *)
  | Nat | Zero | Succ of term
  | NatElim of term * term * term * term

type value =
  | VLambda of (value -> value)
  | VPi of value * (value -> value)
  | VSigma of value * value
  | VPair of value * value
  | VStar
  | VNat
  | VZero
  | VSucc of value

let rec eval (t : term) (ρ : value list) : value =
  match t with
  | Var i -> List.nth ρ i
  | Lambda (a, b) -> VLambda (fun v -> eval b (v :: ρ))
  | App (m, n) ->
      let vm = eval m ρ in
      let vn = eval n ρ in
      (match vm with
       | VLambda f -> f vn
       | _ -> failwith "apply non-function")
  | Pi (a, b) -> VPi (eval a ρ) (fun v -> eval b (v :: ρ))
  (* ... more cases *)
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| **Π types** | Dependent functions |
| **Σ types** | Dependent pairs |
| **Universes** | Type of types (Set, Type₀, ...) |
| **Conversion** | βη-equivalence |
| **Elaboration** | Surface → core |

## Advanced Features

| Feature | Description |
|---------|-------------|
| **Match** | Pattern matching (via NatElim) |
| **Universe polymorphism** | Generic over universes |
| **Cumulativity** | Subtyping between universes |
| **Irrelevance** | Prop irrelevance (SProp) |
| **Observational equality** | UIP, univalence |

## Tips

- Start with simple dependent types
- Implement conversion checking carefully
- Use de Bruijn for binding
- Consider universe constraints
- Handle definitional equality

## Related Skills

- `system-f` - Polymorphic lambda calculus
- `type-inference-engine` - HM inference
- `coq-proof-assistant` - Coq proofs

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| **Coq Reference Manual** | Definitive implementation reference |
| **Martin-Löf, "Intuitionistic Type Theory" (1984)** | Original dependent type theory |
| **Harper & Pfenning, "On Equivalence and Canonical Forms in the LF Type Theory" (2005)** | Type-directed conversion checking |
| **Abel, Coquand & Dybjer, "Normalization by Evaluation for Martin-Löf Type Theory" (2007)** | NbE for dependent types |
| **Chapman, Altenkirch & McBride, "Epigram Reloaded: A Standalone Typechecker for ETT" (2006)** | Elaboration implementation |

## Tradeoffs and Limitations

### Implementation Approach Tradeoffs

| Approach | Pros | Cons |
|----------|------|------|
| **Type checking** | Decidable, simple | Less powerful inference |
| **Type inference** | More convenient | Complex constraint solving |
| **Bidirectional** | Balanced | Still incomplete |

### When NOT to Implement Dependent Types

- **For simple verification**: Use refinement types instead (Liquid Haskell, F*)
- **For performance**: Consider Haskell/OCaml with GADTs
- **For teaching**: Start with System F or STLC

### Complexity Considerations

- **Undecidability**: Full type checking is undecidable for dependent types
- **Universe constraints**: Solving universe constraints is complex
- **Normalization**: Required for conversion; expensive without NbE
- **Type inference**: Principally undecidable; use bidirectional checking

### Limitations

- **Performance**: 10-100x slower than simple types
- **Error messages**: Hard to make comprehensible
- **Termination checking**: Required for soundness (or positivity)
- **Universe levels**: Must handle Level → Level max → etc.
- **Normalization**: Full β-reduction needed for conversion
- **Learning curve**: Users need to understand type theory

## Research Tools & Artifacts

Dependent type systems:

| System | Language | What to Learn |
|--------|----------|---------------|
| **Coq** | OCaml | Production proof assistant |
| **Agda** | Haskell | Dependently typed programming |
| **Idris** | Idris | Type-driven development |
| **Lean** | Lean | Modern proof assistant |
| **NuPRL** | Lisp | Constructive type theory |

### Key Papers

- **Martin-Löf** - Original type theory
- **Coquand** - Calculus of Constructions
- **Harper et al.** - Syntactic theory

## Research Frontiers

### 1. Homotopy Type Theory
- **Goal**: Univalence, higher inductive types
- **Approach**: Path types, identity types
- **Books**: HoTT Book

### 2. Cubical Type Theory
- **Goal**: Computational univalence
- **Approach**: Kan operations, faces

## Implementation Pitfalls

| Pitfall | Real Consequence | Solution |
|---------|-----------------|----------|
| **Universe inconsistency** | Paradoxes | Universe checking |
| **Non-termination** | Unsoundness | Termination check |
| **Conversion inefficiency** | Slow checking | NbE |
