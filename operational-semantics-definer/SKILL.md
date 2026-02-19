---
name: operational-semantics-definer
description: 'Defines operational semantics for programming languages. Use when: (1)
  Designing a new language, (2) Proving properties about language semantics, (3) Implementing
  interpreters.'
version: 1.0.0
tags:
- semantics
- operational-semantics
- pl-foundations
- language-design
difficulty: intermediate
languages:
- ocaml
- coq
- python
dependencies: []
---

# Operational Semantics Definer

Defines small-step and big-step operational semantics for programming languages.

## When to Use

- Designing new programming languages
- Formalizing language semantics
- Proving properties about programs
- Implementing interpreters from specs

## What This Skill Does

1. **Defines syntax** - BNF/EBNF for terms and values
2. **Specifies semantics** - Structural operational semantics (SOS)
3. **Proves properties** - Progress and preservation
4. **Generates interpreters** - Executable semantics

## Implementation

### Big-Step Interpreter

```python
@dataclass
class Store:
    """Memory store: variable -> value"""
    data: dict
    
    def __getitem__(self, x):
        return self.data[x]
    
    def __setitem__(self, x, v):
        return Store({**self.data, x: v})

def eval_expr(e: Expr, s: Store) -> Value:
    match e:
        case Const(n): return n
        case True_(): return True
        case False_(): return False
        case Add(e1, e2):
            v1 = eval_expr(e1, s)
            v2 = eval_expr(e2, s)
            return v1 + v2
        case Eq(e1, e2):
            v1 = eval_expr(e1, s)
            v2 = eval_expr(e2, s)
            return v1 == v2
        case Not(e):
            return not eval_expr(e, s)

def eval_cmd(c: Command, s: Store) -> Store:
    match c:
        case Skip():
            return s
        case Assign(x, e):
            v = eval_expr(e, s)
            return Store({**s.data, x: v})
        case Seq(c1, c2):
            s1 = eval_cmd(c1, s)
            return eval_cmd(c2, s1)
        case If(e, c1, c2):
            if eval_expr(e, s):
                return eval_cmd(c1, s)
            else:
                return eval_cmd(c2, s)
        case While(e, c):
            if eval_expr(e, s):
                s1 = eval_cmd(c, s)
                return eval_cmd(While(e, c), s1)  # Recursive
            else:
                return s
```

### Small-Step Reducer

```python
from typing import Callable

# Configuration: (command, store)
Config = tuple[Command, Store]

def reduce_step(c: Command, s: Store) -> Optional[Config]:
    """Take one step, or return None if stuck"""
    
    match c:
        # E-Contx
        case Seq(Skip(), c2):
            return (c2, s)
        
        case Seq(c1, c2):
            if can_step(c1):
                c1', s1 = step(c1)
                return (Seq(c1', c2), s1)
        
        # E-Assign
        case Assign(x, e) if is_value(e):
            return (Skip(), Store({**s.data, x: eval_expr(e, s)}))
        
        # E-AssignCtx
        case Assign(x, e) if not is_value(e):
            e' = step_expr(e)
            return (Assign(x, e'), s)
        
        # E-IfTrue/False
        case If(e, c1, c2) if is_value(e):
            if eval_expr(e, s):
                return (c1, s)
            else:
                return (c2, s)
        
        # E-While
        case While(e, c):
            return (If(e, Seq(c, While(e, c)), Skip()), s)
    
    return None  # Stuck (no rule applies)

def run_small_step(c0: Command, s0: Store, max_steps=1000):
    """Run program to completion"""
    c, s = c0, s0
    for _ in range(max_steps):
        if is_value(c) and isinstance(c, Skip):
            return s  # Done
        result = reduce_step(c, s)
        if result is None:
            raise RuntimeError(f"Stuck at: {c}")
        c, s = result
    raise RuntimeError("Too many steps")
```

## Key Concepts

### Big-Step (Natural) Semantics

- **Judgment**: ⟨e, s⟩ ⇓ v (expression e in store s evaluates to value v)
- **Pros**: Easier to read, direct connection to interpreters
- **Cons**: Doesn't express non-termination well

### Small-Step (Structural) Semantics  

- **Judgment**: ⟨e, s⟩ → ⟨e', s'⟩ (one step of evaluation)
- **Pros**: Handles non-termination, parallelism, intermediate states
- **Cons**: More rules, can be complex

### Context Rules

Use evaluation contexts to reduce syntactic clutter:

```
Evaluation contexts:
  E = [] | E + e | v + E | not E | if E then c1 else c2
  
  ⟨E[e], s⟩ → ⟨E[e'], s'⟩  if  ⟨e, s⟩ → ⟨e', s'⟩
```

## Tips

- Define values first (what cannot step further)
- Use naming conventions: (⇒) for big-step, (→) for small-step
- Prove progress + preservation for soundness
- Use contexts to simplify small-step rules
- Consider weak vs strong bisimulation

## Properties to Prove

### Progress
If ⊢ e : τ and e is not a value, then there exists e' such that e → e'

### Preservation  
If ⊢ e : τ and e → e', then ⊢ e' : τ

## Related Skills

- `denotational-semantics-builder` - Denotational models
- `hoare-logic-verifier` - Axiomatic semantics
- `lambda-calculus-interpreter` - Lambda calculus semantics

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| **Gordon, "The Denotational Description of Programming Languages" (1979)** | Introductory denotational semantics |
| **Reynolds, "Theories of Programming Languages" (1998)** | Comprehensive semantics text |
| **Winskel, "The Formal Semantics of Programming Languages" (1993)** | Standard textbook |
| **Plotkin, "A Structural Approach to Operational Semantics" (1981)** | Original structural operational semantics |
| **Pierce, "Types and Programming Languages", Ch. 3 (2002)** | Chapter 3 covers operational semantics |

## Tradeoffs and Limitations

### Semantic Approach Tradeoffs

| Approach | Pros | Cons |
|----------|------|------|
| **Big-step (natural)** | Intuitive, interpreter-like | No non-termination, no intermediate states |
| **Small-step (SOS)** | Handles non-termination, parallelism | More rules, can explode |
| **Denotational** | Compositional, algebraic reasoning | Harder to prove properties |

### When NOT to Use Operational Semantics

- **For verification**: Use axiomatic (Hoare) or denotational semantics
- **For infinite states**: Consider pushdown automata or abstract machines
- **For real-time/continuous**: Use timed automata or hybrid systems

### Limitations

- **Non-termination**: Bigstep can't express diverging computations; use small-step
- **State explosion**: Small-step can have many intermediate configurations
- **Parallelism**: Hard to express concurrent semantics (use process calculi)
- **Context rules**: Required for tractable small-step semantics

## Research Tools & Artifacts

Formal semantics in proof assistants:

| Formalization | Proof Assistant | What's Formalized |
|---------------|----------------|-------------------|
| **POPLMark** | Coq | Core lambda calculus, properties |
| **Mechanized Semantics Library** | Coq | Multiple languages |
| **SEtP** | Coq | Stack-based languages |
| ** Ott** | Coq/Isabelle/Agda | Language definitions |
| **Lem** | Coq/Isabelle | Generative definitions |

### Interactive Tools

- **PLT Redex** (Racket) - Semantic definitions, visualization
- **K-framework** - Language definitions, verification
- **Maude** - Rewriting logic semantics

## Research Frontiers

### 1. Parametricity
- **Goal**: Prove properties from typing alone
- **Technique**: Relational parametricity (Reynolds)
- **Papers**: "Types, Abstraction and Parametric Polymorphism" (Reynolds, 1983), "Theorems for Free!" (Wadler, 1989)
- **Application**: Free theorems

### 2. Contextual Equivalence
- **Goal**: Formalize when programs behave the same
- **Technique**: Applicative bisimilarity, environmental bisimilarity
- **Papers**: "Environmental Bisimulations" (Sangiorgi & others)

### 3. Relational Reasoning
- **Goal**: Prove relations between programs
- **Technique**: Logical relations, step-indexed methods
- **Papers**: "Logical Relations for Monadic State" (Birkedal & others)

### 4. Denotational Semantics Integration
- **Goal**: Connect operational and denotational
- **Technique**: Full abstraction proofs
- **Papers**: "Full Abstraction for PCF" (Abramsky, Jagadeesan, Malacaria; Hyland, Ong - independently, 1990s)

## Implementation Pitfalls

| Pitfall | Real Example | Solution |
|---------|-------------|----------|
| **Stuck states** | Semantically invalid final states | Define values first |
| **Non-termination** | Big-step misses non-termination | Use small-step or coinduction |
| **Non-confluence** | Different reduction orders give different results | Prove Church-Rosser |
| **Missing contexts** | Rules don't cover all cases | Use completeness checking |
| **Store passing** | Mutable state requires care | Define store explicitly |

### The "Store" Problem

When adding mutable state, must define store explicitly:

```python
# Configuration includes store
Configuration = (Command, Store)  # Not just Command

# Evaluation contexts for stores
def eval_cmd(c, s):
    match c:
        case Assign(x, e):
            v = eval_expr(e, s)
            return (Skip(), s[x := v])  # Return new store!
```

### The "Big-Step Non-Termination" Gap

Big-step semantics cannot express divergence:

```python
# This loop never produces a result in big-step:
# while true: skip
# No rule produces a value!

# In small-step, we can model it:
# (while true: skip) → (while true: skip)  -- infinite path
```

This is why we need small-step for non-terminating programs!
