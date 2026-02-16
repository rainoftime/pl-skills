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

```coq
(* Coq Implementation *)

(* Core Syntax *)
Inductive term : Type :=
  | tVar : nat -> term
  | tAbs : term -> term
  | tApp : term -> term -> term
  | tPi : term -> term -> term  (* Dependent function *)
  | tSigma : term -> term -> term  (* Dependent pair *)
  | tPair : term -> term -> term
  | tProj1 : term -> term
  | tProj2 : term -> term
  | tStar : term  (* Unit *)
  | tNat : term
  | tZero : term
  | tSucc : term -> term
  | tNatElim : term -> term -> term -> term.

(* Context: list of (name * term * type) *)
Definition context := list (nat * term * term).

(* Type Checking *)
Inductive has_type (Γ : context) : term -> term -> Prop :=
  | T_Var : ∀ x A,
      In (x, A) Γ ->
      has_type Γ (tVar x) A
  | T_Pi : ∀ A B s1 s2,
      has_type Γ A s1 ->
      has_type (Γ ++ [(0, A)]) B s2 ->
      has_type Γ (tPi A B) s2
  | T_Abs : ∀ A B M N s1 s2,
      has_type Γ A s1 ->
      has_type (Γ ++ [(0, A)]) N B ->
      has_type Γ (tAbs (A, N)) (tPi A B)
  | T_App : ∀ M N A B,
      has_type Γ M (tPi A B) ->
      has_type Γ N A ->
      has_type Γ (tApp M N) (B.[0 := N])
  | T_Sigma : ∀ A B s1 s2,
      has_type Γ A s1 ->
      has_type (Γ ++ [(0, A)]) B s2 ->
      has_type Γ (tSigma A B) s2
  | T_Pair : ∀ A B M N,
      has_type Γ M A ->
      has_type Γ N B.[0 := M] ->
      has_type Γ (tPair M N) (tSigma A B)
  | T_Proj1 : ∀ P M A B,
      has_type Γ M (tSigma A B) ->
      has_type Γ (tProj1 M) A
  | T_Proj2 : ∀ P M A B,
      has_type Γ M (tSigma A B) ->
      has_type Γ (tProj2 M) B.[0 := tProj1 M]
  | T_Nat : has_type Γ tNat Type
  | T_Zero : has_type Γ tZero tNat
  | T_Succ : ∀ n,
      has_type Γ n tNat ->
      has_type Γ (tSucc n) tNat
  | T_NatElim : ∀ P m z s,
      has_type Γ P (tPi tNat Type) ->
      has_type Γ z P.[0 := tZero] ->
      has_type Γ s (tPi tNat (tPi P (tPi (tSucc (tVar 0)) P))) ->
      has_type Γ (tNatElim P m z s) (tPi tNat P).

(* Reduction (β) *)
Inductive red : term -> term -> Prop :=
  | R_AppAbs : ∀ M N,
      red (tApp (tAbs M) N) M.[0 := N]
  | R_Proj1 : ∀ M N,
      red (tProj1 (tPair M N)) M
  | R_Proj2 : ∀ M N,
      red (tProj2 (tPair M N)) N
  | R_NatElimSucc : ∀ P m z s n,
      red (tNatElim P (tSucc n) z s) 
          (tApp (tApp (tApp s n) (tNatElim P n z s)) z).

(* Progress Lemma *)
Lemma progress : ∀ M T,
  has_type [] M T ->
  value M \/ ∃ M', red M M'.

(* Preservation Lemma *)  
Lemma preservation : ∀ M M' T,
  has_type [] M T ->
  red M M' ->
  has_type [] M' T.
```

## Elaboration

```coq
(* From surface syntax to core *)

(* Surface: λ(x : A) => e *)
(* Core: tAbs A e *)

Elabulation algorithm:
1. Infer type of binding: A : s
2. Extend context with x : A
3. Elaborate body: e : B
4. Compute result type:
   - Non-dependent: Pi A (λx. B)
   - Dependent: Pi A (λx. B)

(* Pattern matching elaboration *)
Elab match e return P with
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

- `dependent-type-implementer` - CoC
- `type-inference-engine` - HM inference
- `coq-proof-assistant` - Coq proofs

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| **Coq Reference Manual** | Definitive implementation reference |
| **Martin-Löf, "Intuitionistic Type Theory"** | Original dependent type theory |
| **Harper & Pfenning, "On Equivalence and Canonical Forms"** | Conversion checking |
| **Abel et al., "Normalization for Dependent Types"** | Normalization by evaluation |
| **Chapman et al., "Elaborating Dependent Types"** | Elaboration to core language |

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
