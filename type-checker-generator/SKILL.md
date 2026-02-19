---
name: type-checker-generator
description: 'Generates type checkers from language specifications. Use when: (1)
  Designing a new programming language, (2) Adding type checking to an interpreter,
  (3) Implementing core language proofs, (4) Building language prototypes.'
version: 1.0.0
tags:
- type-systems
- type-checking
- compiler
- static-analysis
difficulty: intermediate
languages:
- python
- ocaml
dependencies:
- lambda-calculus-interpreter
---

# Type Checker Generator

Generates sound and complete type checkers from formal type system specifications.

## When to Use

- Designing a new programming language
- Implementing type systems from research papers
- Building interpreters with static type checking
- Proving type soundness properties
- Creating minimal viable languages (MVLs)

## What This Skill Does

1. **Parses type system specifications** - Reads formal rules (typing judgments)
2. **Generates type checker code** - Produces executable type checker
3. **Proves soundness** - Outputs progress + preservation proof sketch
4. **Handles edge cases** - Generates error messages for type errors

## How to Use

1. Specify syntax and declarative typing rules for your language
2. Encode algorithmic checking rules (and inference where needed)
3. Add substitution/unification support for polymorphism
4. Validate with positive/negative tests and meta-theory checks

## Key Concepts

### Type System Components

| Component | Description |
|-----------|-------------|
| **Syntax** | Types (τ) and terms (e) |
| **Typing rules** | Judgments (Γ ⊢ e : τ) |
| **Subtyping** | Type ordering (τ₁ <: τ₂) |
| **Kinding** | Type-level well-formedness |
| **Type errors** | Error messages with locations |

### Soundness Theorem

A type system is **sound** if:
1. **Progress**: A well-typed term is either a value or can take a step
2. **Preservation**: If ⊢ e : τ and e → e', then ⊢ e' : τ

## Implementation Patterns

### Structure

```python
class TypeChecker:
    def __init__(self, type_system: TypeSystem):
        self.type_system = type_system
        self.context = {}
        self.errors = []
    
    def check(self, term: Term) -> Optional[Type]:
        """Main entry point: check term is well-typed"""
        pass
    
    def check_app(self, func: Term, arg: Term) -> Optional[Type]:
        """Check application using T-App rule"""
        pass
    
    def unify(self, t1: Type, t2: Type) -> bool:
        """Unify two types (for inference)"""
        pass
```

### Error Reporting

```python
def type_error(self, term: Term, expected: Type, actual: Type):
    self.errors.append(TypeError(
        location=term.location,
        message=f"Expected {expected}, got {actual}"
    ))
```

## Common Patterns

### Bidirectional Type Checking

Separate into:
- **Checking**: Given τ, verify e : τ (easier)
- **Inferring**: Given e, infer τ (harder)

```python
def synth(self, e: Term) -> Optional[Type]:
    """Synthesis/inference mode"""
    match e:
        case Var(x): return self.lookup(x)
        case App(e1, e2):
            t1 = self.synth(e1)
            t2 = self.check(e2, t1.param_type)  # Check against expected
            return t1.return_type

def check(self, e: Term, tau: Type) -> bool:
    """Checking mode"""
    match e:
        case Lam(x, body):
            self.check(body, tau.body)  # Generalize
        case _:
            tau' = self.synth(e)
            return tau' <= tau  # Subtype check
```

### Constraint-Based Typing

Collect constraints during traversal, solve afterward:

```python
def infer(self, e: Term) -> (Type, Constraints):
    constraints = []
    match e:
        case App(e1, e2):
            t1, c1 = self.infer(e1)
            t2, c2 = self.infer(e2)
            fresh = fresh_type_var()
            constraints.append((t1, Fun(t2, fresh)))
            return (fresh, c1 ++ c2 ++ constraints)
```

## Tips

- Start with the simply-typed lambda calculus (STLC)
- Add products, sums, then polymorphism
- Prove soundness alongside implementation
- Use bidirectional typing for better error messages
- Track source locations for meaningful errors

## Common Issues

| Issue | Solution |
|-------|----------|
| Infinite types | Use occurs check |
| Recursive types | Add μ (fixpoint) or equirecursive |
| Subtyping complexity | Start with nominal, add structural later |
| Error messages | Track term locations, use unification |

## Tradeoffs and Limitations

### Design Tradeoffs

| Approach | Pros | Cons |
|----------|------|------|
| **Bidirectional** | Better error messages, simpler implementation | Less expressive than constraint-based |
| **Constraint-based** | More flexible, principal types | Complex constraint solving |
| ** declarative** | Easy to read specs | Hard to implement efficiently |

### When NOT to Use This Approach

- **For very large codebases**: Consider separate type checker as a service
- **For gradual typing**: Use gradual type inference instead (different algorithm)
- **For dependent types**: Requires theorem proving; see `dependent-type-implementer`
- **For row polymorphism**: See specialized `row-polymorphism` skill

### Limitations

- **Soundness vs completeness**: Type checkers are usually sound (reject some valid programs) but complete checking is undecidable for rich type systems
- **Error localization**: Precise error locations require source tracking throughout
- **Incremental checking**: Not built-in; requires separate infrastructure

## Assessment Criteria

A high-quality type checker implementation should have:

| Criterion | What to Look For |
|-----------|------------------|
| **Soundness** | Never accepts ill-typed programs |
| **Completeness** | Accepts all well-typed programs (when decidable) |
| **Error messages** | Clear, localized, actionable |
| **Type inference** | Principal types when possible |
| **Efficiency** | Linear time for typical programs |
| **Extensibility** | Easy to add new type constructors |
| **Testing** | Property-based tests for inference |

### Quality Indicators

✅ **Good**: Passes all well-typed programs, rejects ill-typed, produces clear errors
⚠️ **Warning**: Incomplete coverage, cryptic error messages, no inference
❌ **Bad**: Soundness bugs, crashes on valid input

## Related Skills

- `type-inference-engine` - Type inference (without annotations)
- `subtyping-verifier` - Verify subtyping relations
- `lambda-calculus-interpreter` - Interpreter for lambda calculi
- `hoare-logic-verifier` - Prove soundness theorems

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| **Pierce, "Types and Programming Languages"** | Definitive textbook on type systems; Ch. 8-15 cover type checking fundamentals |
| **Wright & Felleisen, "A Syntactic Approach to Type Soundness"** | Proof technique for progress + preservation |
| **Cardelli, "Type Systems"** | Comprehensive survey of type system design space |
| **Girard, "Linear Logic"** | Foundation for linear types and resource management |
| **Hindley, "Basic Simple Type Theory"** | Classical reference on polymorphism |

## Research Tools & Artifacts

For implementing type checkers, refer to these research-quality implementations:

| Tool | Language | What to Learn From |
|------|----------|-------------------|
| **OCaml compiler** (ocaml/ocaml) | OCaml | Industrial-strength type inference, module system, GADTs |
| **GHC Haskell** | Haskell | Type inference, type classes, role system |
| **TypeScript compiler** (microsoft/TypeScript) | TypeScript | Gradual typing, union types, inference |
| **Rust compiler** (rust-lang/rust) | Rust | Borrow checking, trait system, lifetimes |
| **Pyright** | Python | Python type stubs, gradual typing |
| **Dafny verifier** | Boogie | Verification-integrated type checking |

### Coq Formalizations (for verification)

- **"Types and Programming Languages" in Coq** - Full formalization of TAPL
- **Coq's kernel** - Certified type checker implementation
- **Iris** (MPI-Freiburg) - Higher-order separation logic

### Relevant Papers with Implementations

- **"Practical Type Inference for the GHC Type System"** (Jones, 2007) - GHC's implementation
- **"Complete and Easy Bidirectional Type Checking"** (Pfenning & Davies, 2001) - The gold standard for bidirectional typing
- **"Extensible records with scoped labels"** (Leijen, 2005) - Practical row polymorphism design

## Research Frontiers

Current active research directions in type checking:

### 1. Gradual Typing & Reliability
- **Key papers**: "Gradual Typing for Functional Languages" (Siek & Taha, 2006), "Reticulated Python" (Vitousek et al.)
- **Challenge**: Blending static and dynamic typing seamlessly
- **Tools**: Pyre (Facebook), mypy, TypeScript

### 2. Bidirectional Type Checking
- **Key papers**: "Reconstructing Type Inference" (Dunfield & Krishnaswami, 2023)
- **Challenge**: Balancing inference power with error messages
- **Tools**: Agda, Idris, Deduce

### 3. Effect Systems & Capabilities
- **Key papers**: "Koka: Programming with Row Polymorphic Effect Types" (Leijen, 2017)
- **Challenge**: Tracking side effects without monads
- **Tools**: Koka, Frank, Eff

### 4. Qualified Types & Type Classes
- **Key papers**: "How to Make Ad-hoc Polymorphism Less Ad-hoc" (Wadler & Blott, 1989)
- **Challenge**: Overloading without violating parametricity
- **Tools**: GHC Haskell, PureScript

## Implementation Pitfalls

Common mistakes in production type checker implementations:

| Pitfall | Real Example | Prevention |
|---------|--------------|------------|
| **Value restriction** | ML's original let-polymorphism allowed unsoundness | Implement value restriction (Wright, 1995) |
| **Unification variable scope** | GHC's unsolved type variables leaking | Maintain level-based scope tracking |
| **Occurs check omission** | Infinite types like `x = List(x)` | Always implement occurs check |
| **Subtyping transitivity** | Complex hierarchies lead to soundness bugs | Test edge cases systematically |
| **Kind inference** | Type-level computation errors | Implement separate kind checking |
| **Infinite loops in inference** | Recursive type definitions | Add depth limits with good error messages |

### The "Value Restriction" Story

The original Hindley-Milner let-polymorphism was unsound:
```ocaml
(* Unsound in original ML *)
let pair = (ref [], ref []) in
let (a, b) = pair in
  a := [1];  (* Add int to list *)
  b := [true]  (* Now a contains bools! *)
```

**Solution**: Only generalize at value bindings (not function arguments). This is why you see `let` vs `let rec` semantics differ in OCaml.

### Principal Types Are Not Always Principal

Even with Hindley-Milner, certain programs have no principal type. Know when to report ambiguity vs. try harder:

```haskell
-- Which type is principal?
f x = [x, x + 1]  -- [Int] or [Num a]?
```
