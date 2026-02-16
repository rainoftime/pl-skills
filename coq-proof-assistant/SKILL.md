---
name: coq-proof-assistant
description: 'Assists with Coq proof development. Use when: (1) Proving program correctness,
  (2) Formalizing mathematics, (3) Verified compilation.'
version: 1.0.0
tags:
- proof-assistant
- coq
- formal-verification
- dependent-types
difficulty: intermediate
languages:
- coq
dependencies: []
---

# Coq Proof Assistant

Assists with interactive proof development in Coq.

## When to Use

- Formal verification
- Program correctness proofs
- Mathematical formalization
- Verified software development

## What This Skill Does

1. **Writes proofs** - Interactive tactic proofs
2. **Structures theories** - Modules, sections
3. **Handles induction** - Complex inductive proofs
4. **Verifies** - Type checking proofs

## Basic Tactics

```coq
(* Basic proof structure *)
Theorem example : forall n : nat, n + 0 = n.
Proof.
  induction n.
  - (* Base case: n = 0 *) reflexivity.
  - (* Inductive case: n = S n' *)
    simpl.
    rewrite IHn.
    reflexivity.
Qed.

(* Common tactics *)
- intros      : Introduce hypotheses
- destruct    : Case analysis
- induction   : Induction
- rewrite     : Rewrite using equality
- apply       : Apply lemma
- exact       : Provide exact term
- reflexivity : Prove equality
- simpl       : Simplify
- unfold      : Unfold definition
- rewrite     : Rewrite
- assert      : Make assertion
- remember    : Remember expression
- generalize  : Generalize over term
```

## Implementation Examples

### List Reversal

```coq
(* Define list reversal *)
Fixpoint rev {A : Type} (l : list A) : list A :=
  match l with
  | nil => nil
  | cons x xs => rev xs ++ cons x nil
  end.

(* Prove correctness *)
Theorem rev_correct : forall A (l : list A),
  rev (rev l) = l.
Proof.
  induction l as [| x xs IH ].
  - (* Base case: l = nil *) reflexivity.
  - (* Inductive case *)
    simpl.
    rewrite <- IH.
    rewrite <- app_assoc.
    simpl.
    reflexivity.
Qed.

(* More efficient version with accumulator *)
Fixpoint rev_append {A : Type} (l acc : list A) : list A :=
  match l with
  | nil => acc
  | cons x xs => rev_append xs (cons x acc)
  end.

Definition rev' {A : Type} (l : list A) := rev_append l nil.

Lemma rev_append_rev : forall A (l acc : list A),
  rev_append l acc = rev l ++ acc.
Proof.
  induction l; intros.
  - simpl. reflexivity.
  - simpl. rewrite IHl. rewrite app_assoc. reflexivity.
Qed.
```

### Binary Search Tree Verification

```coq
(* BST definition *)
Inductive bst (key : Set) (R : key -> key -> Prop) : key -> Prop :=
  | bst_empty : bst key R EmptyKey
  | bst_node : forall k v l r,
      bst key R l ->
      bst key R r ->
      (forall k', In key l k' -> R k' k) ->
      (forall k', In key r k -> R k k') ->
      bst key R k.

(* Insert preserves BST *)
Lemma bst_insert_preserves : forall key R (H: StrictOrder R) 
  k v (t : bst key R k),
  bst key R (insert k v t).
Proof.
  induction t; intros.
  - constructor; auto.
  - destruct (compare_dec k0 k) as [H'|H'|H'].
    + (* k < k0: insert in left *)
      constructor; auto.
      * apply IHt1; auto.
      * intros. apply H1. left; auto.
    + (* k = k0: replace *)
      constructor; auto.
    + (* k > k0: insert in right *)
      constructor; auto.
      * apply IHt2; auto.
      * intros. apply H1. right; auto.
Qed.
```

### Compiler Verification

```coq
(* Simple expression language *)
Inductive expr : Type :=
  | EConst : nat -> expr
  | EPlus : expr -> expr -> expr
  | EVar : nat -> expr.

(* Target: stack machine *)
Inductive instr : Type :=
  | IPush : nat -> instr
  | IAdd : instr
  | ILoad : nat -> instr.

Definition prog := list instr.

(* Compiler *)
Fixpoint compile (e : expr) : prog :=
  match e with
  | EConst n => IPush n :: nil
  | EPlus e1 e2 => compile e2 ++ compile e1 ++ IAdd :: nil
  | EVar x => ILoad x :: nil
  end.

(* Compiler correctness *)
Inductive stack : Type := stack (l : list nat).

Inductive exec : prog -> stack -> stack -> Prop :=
  | exec_nil : forall s, exec nil s s
  | exec_push : forall n s s', 
      s' = stack (n :: s.(l)) ->
      exec (IPush n :: p) s s'
  | exec_add : forall n1 n2 s s',
      s = stack (n2 :: n1 :: s'.(l)) ->
      s' = stack (n1 + n2 :: s'.(l)) ->
      exec (IAdd :: p) s s'.

Lemma compile_correct : forall e s,
  exec (compile e) s (stack (eval e :: s.(l))).
Proof.
  induction e; intros; simpl.
  - (* EConst *) constructor. simpl. constructor.
  - (* EPlus *)
    rewrite IHe1, IHe2.
    constructor. reflexivity.
    constructor. reflexivity.
    constructor.
  - (* EVar *) constructor. reflexivity.
Qed.
```

## Advanced Tactics

```coq
(* Automation *)
Hint Resolve bst_node bst_empty.
Hint Constructors bst exec.

(* CustomLtac *)
Ltac solve_by_ :=
  match goal with
  | [ H : ?P -> ?Q -> ?R |- ?R ] =>
    let H' := fresh in
    assert (H' : P); [|assert H0 : Q; [|exact (H H' H0)]]
  end.

(* Induction on complex structure *)
Lemma foo : forall l, P l.
Proof.
  induction l as [| x xs IHxs ].
  - (* nil *) ...
  - (* cons *) ...
    (* Use IH on subterm *)
    apply IHxs.
    (* Or generalize before induction *)
    generalize dependent l.
    induction x; ...
Qed.

(* Structuring large proofs *)
Section MySection.
  Variable A : Type.
  
  Lemma lemma1 : P A.
  Proof. ... Qed.
  
  Lemma lemma2 : Q A.
  Proof. ... using lemma1. ...
End MySection.
```

## Key Tactics Reference

| Tactic | Description |
|--------|-------------|
| `intros` | Introduce variables/hypotheses |
| `apply` | Apply lemma/hypothesis |
| `exact` | Give exact term |
| `refine` | Give term with holes |
| `destruct` | Case analysis |
| `induction` | Induction |
| `rewrite` | Rewrite equality |
| `simpl` | Simplify |
| `unfold` | Unfold definition |
| `assert` | Make assertion |
| `cut` | Cut lemma |
| `inversion` | Inversion |
| `econstructor` | Eapply constructor |
| `lia` | Linear integer arithmetic |
| `omega` | Omega solver |
| `auto` | Auto proof search |
| `eauto` | Eager auto |
| `tauto` | Classical tautologies |
| `congruence` | Equality/congruence |

## Tips

- Start simple, add complexity
- Use `Hint` for automation
- Structure with sections
- Use named hypotheses
- Prove lemmas first
- Check with `Check`

## Related Skills

- `dependent-type-implementer` - Type theory
- `llvm-backend-generator` - Verified compilers
- `hoare-logic-verifier` - Verification

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| **Bertot & Castéran, "Interactive Theorem Proving and Program Development"** | Coq's standard textbook; comprehensive Coq development |
| **Chlipala, "Certified Programming with Dependent Types"** | Practical IDP (Interactive Density Polymorphism) techniques |
| **Pierce et al., "Software Foundations"** | Building verified software in Coq, volumes 1-4 |
| **The Coq Proof Assistant Reference Manual** | Official documentation |
| **Gonthier & Werner, "A Machine-Checked Proof of the Four Color Theorem"** | Large-scale proof engineering |

## Tradeoffs and Limitations

### Approach Tradeoffs

| Approach | Pros | Cons |
|----------|------|------|
| **Interactive (tactic)** | Flexible, large proofs | Requires expertise |
| **Declarative** | Readable, audit-able | Less automation |
| **Embedded** | Programmatic | Harder to maintain |

### When NOT to Use Coq

- **For simple properties**: Testing may be cheaper
- **For automated verification**: Consider SAT/SMT solvers (z3, cvc5)
- **For production code**: Consider formal methods tools (Frama-C, SPARK)
- **For proof automation**: Consider Lean or Isabelle (more powerful automation)

### Complexity Considerations

- **Proof complexity**: Scales with property complexity; large proofs require structure
- **Compilation time**: Large developments can take hours to compile
- **Export**: Can extract to OCaml, Haskell, Scheme

### Limitations

- **Learning curve**: Steep; requires understanding dependent types, tactics
- **Scalability**: Large proofs can become slow and hard to maintain
- **Automation**: Less than SMT solvers; requires manual guidance
- **Extraction**: Code extraction must be verified for correctness

## Assessment Criteria

Quality Coq development should have:

| Criterion | What to Look For |
|-----------|------------------|
| **Correctness** | Proof verifies the property |
| **Readability** | Clear structure, good names |
| **Maintainability** | Easy to modify |
| **Automation** | Appropriate use of hints |
| **Extraction** | Correct extracted code |
| **Performance** | Compiles in reasonable time |

### Quality Indicators

✅ **Good**: Sound proofs, clear structure, good automation
⚠️ **Warning**: Opaque proofs, poor naming
❌ **Bad**: Unproven assertions, extraction errors

## Research Tools & Artifacts

Coq ecosystem:

| Tool | What to Learn |
|------|---------------|
| **Coq** | Proof assistant |
| **MathComp** | Mathematical components |
| **VST** | Verified C |

## Research Frontiers

### 1. Metaprogramming
- **Approach**: Program the proof assistant
- **Papers**: "Mtac" (various)

## Implementation Pitfalls

| Pitfall | Real Consequence | Solution |
|---------|-----------------|----------|
| **Proof obsolescence** | Breakage with updates | Use opam |
