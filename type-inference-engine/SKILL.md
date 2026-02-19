---
name: type-inference-engine
description: 'Implements Hindley-Milner type inference. Use when: (1) Adding type
  inference to a functional language, (2) Understanding ML-style let-polymorphism,
  (3) Implementing constraint-based type systems.'
version: 1.0.0
tags:
- type-systems
- type-inference
- hindley-milner
- unification
difficulty: intermediate
languages:
- python
- ocaml
dependencies:
- type-checker-generator
---

# Type Inference Engine

Implements complete Hindley-Milner (HM) type inference with let-polymorphism.

## When to Use

- Implementing ML, Haskell, or OCaml-style type inference
- Building functional language interpreters
- Learning type inference algorithms
- Extending languages with polymorphism

## What This Skill Does

1. **Implements unification** - First-order unification with occurs check
2. **Generates constraints** - Collects type equations from terms
3. **Solves constraints** - Most general unifier (MGU)
4. **Handles polymorphism** - Generalizes let-bound polymorphism

## How to Use

1. Define your term and type syntax (`Var`, `Lam`, `App`, `Let`, etc.)
2. Implement unification with an occurs check
3. Add generalization at `let` bindings and instantiation at variable lookup
4. Run inference and pretty-print the principal type

```python
def infer(term, env):
    match term:
        case Let(x, e1, e2):
            t1, c1 = infer(e1, env)
            sigma = solve(c1)
            t1 = apply_subst(sigma, t1)
            env1 = apply_subst_env(sigma, env)
            scheme = generalize(t1, env1)
            t2, c2 = infer(e2, {**env1, x: scheme})
            return (t2, compose(c2, sigma))
    raise ValueError(f"unknown term: {term}")
```

### Let-Polymorphism

```python
@dataclass
class Scheme:
    """Type scheme with quantified variables"""
    vars: list[TypeVar]
    body: Type

def generalize(t: Type, env: dict) -> Scheme:
    """Generalize type to scheme"""
    ftv_t = free_type_vars(t)
    ftv_env = set()
    for s in env.values():
        ftv_env |= free_type_vars_of_scheme(s)
    quant_vars = ftv_t - ftv_env
    return Scheme(list(quant_vars), t)

def instantiate(scheme: Scheme) -> Type:
    """Instantiate quantified type with fresh vars"""
    mapping = {v: fresh() for v in scheme.vars}
    return substitute(scheme.body, mapping)
```

## Key Concepts

### Unification

The core algorithm for type inference:

| Property | Description |
|----------|-------------|
| **Soundness** | If unify(s, t) = σ, then apply(σ, s) = apply(σ, t) |
| **Most General** | σ is most general among all unifiers |
| **Occurs Check** | Prevents infinite types (x = List(x)) |

### Principal Types

HM guarantees **principal types**: the most general type that all others can be specialized to.

### Constraint Solving

Collect constraints, then solve:

```
e = λf. (λx. x) (λy. f y)

Constraint generation:
  f : α, x : β, x : γ → δ
  β = γ → δ  (from App(λx.x, ...))
  α = γ → ε
  ε = δ     (from App(f, y))

Solution:
  α = β → β  (id)
```

## Tips

- Use union-find for efficient unification
- Implement occurs check to prevent infinite types
- Track free type variables for generalization
- Handle let-polymorphism correctly
- Print types with pretty-printing

## Common Issues

| Issue | Solution |
|-------|----------|
| Infinite types | Add occurs check |
| Ambiguous types | Use fresh variables |
| Poor error messages | Record constraint origins |
| Slow unification | Use union-find structure |

## Related Skills

- `type-checker-generator` - Generate type checkers
- `dependent-type-implementer` - System F polymorphism
- `gradual-typing-implementer` - Gradual typing

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| **Milner, "A Theory of Type Polymorphism in Programming" (1978)** | Original Hindley-Milner paper; let-polymorphism |
| **Damas & Milner, "Principal Type Schemes for Functional Languages" (POPL 1982)** | Algorithm J for principal types |
| **Hindley, "The Principal Type-Scheme of an Object in Combinatory Logic" (1969)** | Original HM work |
| **Jones, "Practical Type Inference for GHC" (2007)** | GHC Haskell's type inference |
| **Peyton Jones, "The GHC Type System" (2003)** | Modern extensions to HM |

## Research Tools & Artifacts

Real-world type inference implementations to study:

| System | Language | Key Technique |
|--------|----------|--------------|
| **GHC Haskell** | Haskell | Constraint-based inference, aggressive optimization |
| **OCaml compiler** | OCaml | Classical HM with extensions |
| **Scala 3** | Scala | Constraint-based, union types, match types |
| **TypeScript** | TypeScript | Flow analysis, contextual typing |
| **Pyright** | Python | Stub-based, precise type narrowing |
| **Dylan** | Dylan | CLOS integration, multiple dispatch |

### Papers with Available Implementations

- **"Practical Type Inference for GHC"** - GHC's actual implementation
- **"OutsideIn(X)"** - GHC's external core approach (Peyton Jones et al.)
- **"Complete and Easy Bidirectional Type Checking"** - The "Dungeons" paper

### Interactive/Infrastructure

- **GHC's constraint solver** - Most sophisticated in production
- **OCaml's typecore** - Clean, readable implementation  
- **Hindley** (Hackage) - Educational Haskell implementation

## Research Frontiers

### 1. Constraint-Based Type Inference
- **Approach**: Generate constraints, solve separately
- **Advantage**: Separation allows different solving strategies
- **Papers**: "Constraint-Based Type Inference" (Ely 1990s work)
- **GHC uses**: "OutsideIn" modular approach

### 2. Unification-Focused Inference
- **Approach**: In-place unification during traversal
- **Advantage**: Simpler, more direct
- **Papers**: Original HM papers
- **OCaml uses**: This approach

### 3. Lazy Constraint Solving
- **Approach**: Defer solving until needed
- **Advantage**: Better error messages, more complete inference
- **Papers**: "Lazy Rank 2" (Jones, 1997)
- **Used in**: GHC for higher-rank types

### 4. Bidirectional + Inference Hybrids
- **Approach**: Use bidirectional for speed, inference for complex cases
- **Advantage**: Best of both worlds
- **Papers**: "Complete and Easy Bidirectional Type Checking"
- **Used in**: Agda, Idris, Python (pyright)

## Implementation Pitfalls

Real-world type inference failures and how to avoid them:

| Pitfall | Real System Bug | Solution |
|---------|----------------|----------|
| **Value restriction** | Original ML was unsound | Only generalize at `let` (not `fun`), implement value restriction |
| **Flexible vs rigid type variables** | GHC's "rigid vs flexible" errors | Track variable rigidity carefully |
| **Level-based scope** | Type variables leaking between scopes | Maintain level stack (OCaml, GHC) |
| **Ambiguity detection** | "Cannot infer type" without helpful info | Track occurrence positions |
| **Let-generalization** | Over-generalization causes runtime errors | Conservative generalization |
| **Impredicative polymorphism** | Complex interactions | Avoid or use constraint solving |

### The Value Restriction Deep Dive

This is THE classic pitfall - learn it well:

```ocaml
(* UNSOUND in original ML (1978) *)
let r = ref (fun x -> x) in    (* r : ('a -> 'a) ref *)
let _ = r := (fun x -> x + 1) in  (* Now r : (int -> int) ref *)
let f = !r in f true  (* Type error at runtime! *)

(* Fixed: value restriction - only generalize values *)
let r = ref (fun x -> x)    (* ERROR: ref is not a value! *)
let r = let f = fun x -> x in ref f  (* OK: f is a value *)
```

### Occurs Check Failures

Another critical pitfall:

```haskell
-- This should fail with "occurs check"
data Fix a = Fix (Fix a)  -- Infinite type

-- But in practice, causes:
-- "Occurs check: cannot construct the infinite type"
```

### Constraint Solving Order Matters

GHC's "flattening" approach is critical:

```haskell
-- Constraint: f :: (a -> b) -> [a] -> [b]
-- Flatten to: [a] -> [b], a -> b
-- Solve in order: a -> b first, then [a] -> [b]
```

## Connections to Modern Type Systems

HM inference connects to many modern systems:

| Modern System | HM Connection |
|--------------|---------------|
| **Rust's trait system** | Extension of HM with traits |
| **Scala 3** | HM + union types + match types |
| **TypeScript** | HM + structural typing + inference |
| **Swift** | HM + protocols (like traits) |
| **Kotlin** | HM + variance annotations |
