---
name: linear-type-implementer
description: 'Implements linear lambda calculus with linear types. Use when: (1) Building
  resource-aware languages, (2) Quantum programming, (3) Verified memory management.'
version: 1.0.0
tags:
- type-systems
- linear-types
- resource-management
- rust
difficulty: advanced
languages:
- python
- rust
- haskell
dependencies:
- simply-typed-lambda-calculus
---

# Linear Type Implementer

Implements linear logic and linear lambda calculus.

## When to Use

- Resource-aware programming
- Quantum computing (Quipper)
- Verified memory management
- Session types
- Database connections

## What This Skill Does

1. **Implements linear functions** - Use exactly once
2. **Handles affine types** - Use at most once
3. **Provides modalities** - ! (of course), ? (why not)
4. **Enforces linearity** - Every variable used exactly once

## Core Theory

```
Linear Logic:
  - A ⊗ B     : Times (pair)
  - A & B     : With (product)
  - A ⊕ B     : Plus (sum)
  - A ⅋ B     : Par (implication dual)
  - !A        : Of course (persistent)
  - ?A        : Why not (consumable)
  - A → B     : Linear implication (!A ⊢ B)

Linear Lambda Calculus:
  λx. e      : Linear abstraction
  x • y      : Multiplicative application
```

## Implementation

```ocaml
(* Linear type system *)

type linear_term =
  | LVar of string
  | LAbs of string * linear_term
  | LApp of linear_term * linear_term
  | LPair of linear_term * linear_term
  | LFst of linear_term
  | LSnd of linear_term
  | LInl of linear_term
  | LInr of linear_term
  | LCase of linear_term * linear_term * linear_term
  | LLet of string * linear_term * linear_term
  | LNil

type linear_type =
  | LBase
  | LFun of linear_type * linear_type      (* A → B (linear) *)
  | LWith of linear_type * linear_type     (* A & B *)
  | LTimes of linear_type * linear_type    (* A ⊗ B *)
  | LPlus of linear_type * linear_type     (* A ⊕ B *)
  | LOne                                   (* Unit *)
  | LModal of linear_type                   (* !A *)

(* Context: linear (used once) or affine (used 0 or 1) *)
type linear_context = (string * linear_type * usage) list
and usage = Linear | Affine

(* Type checking with substructural logic *)
let rec check_linear (ctx : linear_context) (t : linear_term) (ty : linear_type) : bool =
  match t, ty with
  | LAbs (x, body), LFun (a, b) ->
      let ctx' = add_binding ctx x a Linear in
      check_linear ctx' body b
      
  | LPair (m, n), LTimes (a, b) ->
      check_linear ctx m a && check_linear ctx n b
      
  | LFst p, LWith (a, _) ->
      check_linear ctx p (LWith (a, LBase))
      
  | LSnd p, LWith (_, b) ->
      check_linear ctx p (LWith (LBase, b))
      
  | LLet (x, m, n), b ->
      (* Linear let: consume m exactly once *)
      check_linear ctx m (infer_linear ctx m) &&
      let ctx' = remove_binding ctx x in
      check_linear ctx' n b
      
  | _ -> false

(* Every variable must be used exactly once *)
let check_usage (ctx : linear_context) (t : linear_term) : bool =
  let uses = count_uses t in
  List.for_all (fun (x, _, usage) ->
    match usage with
    | Linear -> uses x = 1  (* Exactly once *)
    | Affine -> uses x <= 1 (* At most once *)
  ) ctx
```

## Linear Logic connectives

```ocaml
(* Linear logic operations *)

(* Tensor (⊗) - independent resources *)
let tensor (a : linear_type) (b : linear_type) : linear_type =
  LTimes (a, b)

(* With (&) - can choose either *)
let with_type (a : linear_type) (b : linear_type) : linear_type =
  LWith (a, b)

(* Plus (⊕) - tagged union *)
let plus (a : linear_type) (b : linear_type) : linear_type =
  LPlus (a, b)

(* Of course (!) - reusable *)
let of_course (a : linear_type) : linear_type =
  LModal a

(* Linear implication: A ⊸ B = !A → B *)
let linear_imply (a : linear_type) (b : linear_type) : linear_type =
  LFun (of_course a, b)
```

## Evaluation

```ocaml
(* Linear evaluator *)
type linear_value =
  | VLam of (linear_value -> linear_value)
  | VPair of linear_value * linear_value
  | VInl of linear_value
  | VInr of linear_value
  | VUnit
  | VRef of int  (* Reference cell *)

let rec eval (t : linear_term) (ρ : linear_value list) : linear_value =
  match t with
  | LVar i -> List.nth ρ i
  
  | LAbs (x, body) ->
      VLam (fun v -> eval body (v :: ρ))
      
  | LApp (m, n) ->
      (match eval m ρ with
       | VLam f -> f (eval n ρ)
       | _ -> failwith "linear apply")
      
  | LPair (m, n) ->
      VPair (eval m ρ, eval n ρ)
      
  | LLet (x, m, n) ->
      let v = eval m ρ in
      (* Important: consume the value! *)
      consume v;
      eval n (v :: ρ)
      
  | LNil -> VUnit

(* Consumption - linear values cannot be duplicated *)
and consume (v : linear_value) : unit =
  match v with
  | VRef r ->
      (* Mark reference as used *)
      ref_used r := true
  | VPair (a, b) ->
      consume a; consume b
  | _ -> ()
```

## Linear Resources

```ocaml
(* Resource management example *)

(* File handle linear type *)
type file_handle = { fd : int }

(* Linear file operations *)
let open_file (path : string) : file_handle =
  { fd = Unix.openfile path [Unix.O_RDONLY] 0 }

let close_file (h : file_handle) : unit =
  Unix.close h.fd

(* Linear read - consumes handle *)
let read_file (h : file_handle) : string * file_handle =
  let buf = Bytes.create 100 in
  let n = Unix.read h.fd buf 0 100 in
  (Bytes.sub_string buf 0 n, h)

(* Usage: must use exactly once *)
let process_file (path : string) =
  let h = open_file path in
  let content, h' = read_file h in
  close_file h';  (* Must close exactly once *)
  content
```

## Quantum Computing Application

```ocaml
(* Linear types for quantum computing (Quipper) *)

(* Qubit: linear (cannot duplicate) *)
type qubit = Q of int

(* Quantum gate: linear function *)
let hadamard (q : qubit) : qubit =
  (* Creates superposition - still linear! *)
  apply_gate H q

(* Linear map *)
let quantum_not (q : qubit) : qubit =
  apply_gate X q

(* Measurement - consumes qubit, returns classical bit *)
let measure (q : qubit) : bool =
  (* Collapse superposition - qubit is consumed *)
  Random.bool ()  (* Simplified *)
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| **Linear** | Use exactly once |
| **Affine** | Use 0 or 1 times |
| **⊗ (tensor)** | Independent resources |
| **& (with)** | Can select |
| **⊕ (plus)** | Tagged choice |
| **! (of course)** | Unlimited use |

## Duplication Handling

| Strategy | Description |
|----------|-------------|
| **Linear** | No duplication |
| **Affine** | Copy at most once |
| **Relevant** | Must use |
| **Ordered** | Sequential use |

## Tips

- Track variable usage carefully
- Handle modality (!) for sharing
- Consider copyable types
- Implement borrowing (like Rust)

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| **Girard, "Linear Logic" (Theoretical Computer Science, 1987)** | Original linear logic foundation |
| **Abramsky, "Computational Interpretations of Linear Logic" (1993)** | Semantic foundations for programming |
| **Wadler, "Linear Types Can Change the World!" (2000)** | Linear types in programming |
| **Baker, "Use-Once Variables and Linear Objects" (1994)** | Linear objects and resources |

## Related Skills

- `session-type-checker` - Session types
- `ownership-type-system` - Rust-style ownership
- `effect-type-system` - Effect tracking

## Research Tools & Artifacts

Linear type implementations:

| System | Language | What to Learn |
|--------|----------|---------------|
| **Linear Haskell** | Haskell | Quotation |
| **Idris 2** | Idris | Linear types |
| **Quipper** | Haskell | Quantum computing |
| **Rust** | Rust | Ownership/borr |

### Key Papers

- **Girard** - Linear logic
- **Wadler** - Linear types in programming

## Research Frontiers

### 1. Linear Type Systems
- **Goal**: Resource safety
- **Approach**: Modal types

## Implementation Pitfalls

| Pitfall | Real Consequence | Solution |
|---------|-----------------|----------|
| **Wrong linearity** | Resource leaks | Check usage |
