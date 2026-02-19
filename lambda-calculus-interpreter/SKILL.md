---
name: lambda-calculus-interpreter
description: 'Implements untyped and simply-typed lambda calculus interpreters. Use
  when: (1) Learning foundations of PL, (2) Implementing functional language features,
  (3) Studying evaluation strategies.'
version: 1.0.0
tags:
- interpreter
- lambda-calculus
- functional-programming
- foundations
difficulty: beginner
languages:
- python
dependencies: []

# Actionable triggers
triggers:
  - "implement a lambda calculus interpreter"
  - "build an interpreter for untyped lambda calculus"
  - "understand beta reduction implementation"
  - "learn call-by-value vs call-by-name"
  - "implement closures in an interpreter"

# Ready-to-use prompts
action_prompts:
  - "Implement a call-by-value interpreter for untyped lambda calculus in Python with Var, Abs, App AST nodes and closure environment"
  - "Add call-by-name lazy evaluation to my lambda calculus interpreter with thunk implementation"
  - "Add Church numerals and arithmetic (add, multiply) to lambda calculus interpreter"
  - "Implement simply-typed lambda calculus with type checking"

# Optional slash commands
commands: []

# Script for direct execution
script: examples/interpreter.py
---

# Lambda Calculus Interpreter

> **Status**: Ready to use | **Auto-trigger**: Yes | **Script**: `python examples/interpreter.py`

## Triggers

This skill activates when user mentions:
- Implementing lambda calculus interpreters
- Building functional language interpreters
- Understanding beta reduction, closures
- Learning evaluation strategies (CBV, CBN)

## Action Prompts

Use these prompts directly:

```
Implement a call-by-value lambda calculus interpreter with:
- Var, Abs, App AST nodes using dataclasses
- Environment-based closure implementation
- Beta reduction with proper substitution
- Support for Church numerals
```

```
Add call-by-name lazy evaluation to existing interpreter:
- Implement Thunk class for delayed evaluation
- Memoize forced thunks
- Compare performance with call-by-value
```

```
Extend interpreter with:
- Fixed-point combinator (Y combinator) for recursion
- Simple type system (Bool, Int, Fun types)
- Type inference using bidirectional checking
```

## When to Use

- Learning functional programming foundations
- Implementing interpreters for functional languages
- Studying evaluation strategies (CBV, CBN, parallel)
- Exploring meta-programming concepts

## What This Skill Does

1. **Parses lambda terms** - Concrete → abstract syntax
2. **Implements reductions** - β-reduction, η-reduction
3. **Handles closures** - Captures lexical environment
4. **Compares strategies** - Call-by-value, call-by-name, etc.

### Church Encoding Implementation

```python
def church_to_int(n):
    """Convert Church numeral to integer"""
    # Church numeral n is λf. λx. f^n(x)
    # Apply to successor function and zero
    succ = lambda x: x + 1
    return n(succ)(0)

def int_to_church(n):
    """Convert integer to Church numeral"""
    # Build: λf. λx. f(f(...f(x)...)) with n applications
    return lambda f: lambda x: f**n(x) if hasattr(f, '__pow__') else None

# Church arithmetic
church_add = Abs("m", Abs("n", 
    Abs("f", Abs("x", 
        App(App(Var("m"), Var("f")), 
            App(App(Var("n"), Var("f")), Var("x")))))))

church_mult = Abs("m", Abs("n", 
    Abs("f", 
        App(Var("m"), App(Var("n"), Var("f"))))))

church_pred = Abs("n", 
    Abs("f", Abs("x",
        App(
            App(App(Var("n"), 
                   Abs("g", Abs("h", App(Var("h"), App(Var("g"), Var("f")))))),
                Abs("u", Var("x"))),
            Abs("u", Var("u"))))))
```

### Simply-Typed Lambda Calculus (STLC)

```python
# Types
TInt = "int"
TBool = "bool"
TFun = lambda t1, t2: ("fun", t1, t2)

def type_check(t: Term, env: dict) -> Type:
    """Simply-typed lambda calculus type checker"""
    
    match t:
        case Var(x):
            return env[x]
        
        case Abs(param, body):
            # Analyzed from context
            pass
        
        case App(func, arg):
            tf = type_check(func, env)
            if not isinstance(tf, tuple) or tf[0] != "fun":
                raise TypeError(f"Cannot apply non-function: {tf}")
            _, dom, cod = tf
            ta = type_check(arg, env)
            if ta != dom:
                raise TypeError(f"Argument type mismatch: {ta} ≠ {dom}")
            return cod
    
    raise ValueError(f"Unknown term: {t}")

# STLC with type inference (bidirectional)
def synth(t: Term, env: dict) -> tuple[Type, list[Constraint]]:
    """Synthesize type"""
    match t:
        case Var(x):
            return (env[x], [])
        
        case App(e1, e2):
            a = fresh_tvar()
            t1, c1 = synth(e1, env)
            t2, c2 = check(e2, t1[1], env)  # Check arg against domain
            return (t1[2], c1 + c2 + [(t1, ("fun", t2, a))])
        
        # ... more cases

def check(t: Term, expected: Type, env: dict) -> tuple[None, list[Constraint]]:
    """Check term has expected type"""
    match t, expected:
        case Abs(param, body), ("fun", dom, cod):
            return check(body, cod, {**env, param: dom})
        
        case _:
            t, c = synth(t, env)
            return (None, c + [(t, expected)])
```

## Test Cases

| Input Term | Expected Result | Description |
|------------|----------------|-------------|
| `(λx. x) (λy. y)` | Closure(λy. y, {}) | Identity applied to identity |
| `(λx. λy. x) (λz. z)` | Closure(λy. x, {x: Closure(λz.z)}) | Constant function |
| `(λx. x x) (λx. x x)` | Diverges | Omega combinator (Ω = ω ω, where ω = λx. x x) |
| `(λf. λx. f x) (λy. succ y)` | Closure(λx. f x, {f: Closure(λy. succ y)}) | Function application |

### Using the Script

```bash
# Run the interpreter
cd lambda-calculus-interpreter
python examples/interpreter.py --help

# Run with custom input
python examples/interpreter.py --input "(λx. x) (λy. y)" --strategy cbv
```

## Evaluation Strategies

| Strategy | Description | Example |
|----------|-------------|---------|
| **Normal order** | Reduce leftmost-outermost first | CBN |
| **Applicative order** | Reduce arguments first | CBV |
| **Weak reduction** | Don't reduce under lambdas | Most implementations |
| **Plotkin's strategies** | CBV, CBN, parallel | Research |

## Tips

- Use de Bruijn indices to avoid alpha-renaming
- Implement environments as immutable maps
- Consider sharing (pointers) for efficiency
- Add letrec for recursion (fixed-point)
- Trace reductions for debugging

## Reduction Semantics

```python
# Explicit substitution
def subst(t: Term, x: str, s: Term) -> Term:
    """Substitute s for x in t"""
    match t:
        case Var(y) if y == x:
            return s
        case Var(y):
            return t
        case Abs(y, body) if y != x:
            return Abs(y, subst(body, x, s))
        case App(e1, e2):
            return App(subst(e1, x, s), subst(e2, x, s))
        case _:
            return t

# β-reduction step
def beta_step(t: Term) -> Term:
    """One step of β-reduction"""
    match t:
        case App(Abs(x, body), arg):
            return subst(body, x, arg)  # β-redex
        # ... add congruence rules
```

## Related Skills

- `operational-semantics-definer` - Language semantics
- `type-inference-engine` - Hindley-Milner
- `simply-typed-lambda-calculus` - STLC with types

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| **Barendregt, "The Lambda Calculus"** | Definitive reference on λ-calculus variants |
| **Pierce, "Types and Programming Languages"** | Chapters 5-7 cover untyped and simply-typed λ-calculus |
| **Plotkin, "Call-by-Name, Call-by-Value and the λ-calculus"** | Formalizes evaluation strategies |
| **Reynolds, "Theories of Programming Languages"** | Comparative study of λ-calculus semantics |
| **Wadsworth, "Semantics and Pragmatics of the Lambda Calculus"** | Original CBV normalization theory |

## Research Tools & Artifacts

For lambda calculus implementations, these are the gold-standard references:

| Implementation | What to Learn |
|----------------|---------------|
| **Standard ML of New Jersey** | Efficient CBV, lazy compilation |
| **OCaml's lambda IR** | Practical intermediate representation |
| **GHC Core** | Optimization-oriented lambda calculus |
| **Lamping/Gonthier optimal reduction** | Optimal graph reduction via interaction nets |
| **Lispkit Lisp** | SECD machine implementation |

### Interactive Lambda Calculus Environments

- **Lambda Calculi Tool** (Cambridge) - Visualization of reductions
- **Proof assistants**: Coq, Agda, Lean for formalizing lambda calculus
- **LEAP** (Lambda, Evaluation, Application, Programming) - Educational framework

## Research Frontiers

### 1. Optimal Reduction
- **Goal**: Reduce to normal form with minimal work
- **Key technique**: Sharing via graphs, not trees
- **Paper**: "An Algorithm for Optimal Lambda Calculus Reduction" (Lamping, POPL 1990)
- **Implementation**: Interaction nets, Gonthier et al. refinement

### 2. Explicit Substitutions
- **Goal**: Formalize substitution as a computational step
- **Key technique**: Environments, stacks, closures
- **Paper**: "Explicit Substitutions" (Abadi, Cardelli, Curien, 1991)
- **Why it matters**: Foundation for implementing functional languages

### 3. Normalization by Evaluation (NbE)
- **Goal**: Efficiently compute normal forms
- **Key technique**: Interpret in a continuation-based meta-language
- **Paper**: "Normalization by Evaluation" (Berger & Schwichtenberg, 1991)
- **Implementation**: Agda, Coq, Dedukti

### 4. Abstract Machines
- **Goal**: Bridge lambda calculus and real execution
- **Key technique**: SECD, Krivine, CAM
- **Paper**: "The Mechanical Evaluation of Expressions" (Landin, 1964), "A call-by-name lambda-calculus machine" (Krivine, 1985; published 2007)
- **Implementation**: Most functional language compilers

## Implementation Pitfalls

The following traps have caused real bugs in production systems:

| Pitfall | Real Consequence | Solution |
|---------|-----------------|----------|
| **Capture-avoiding substitution** | Subtle bugs with alpha-equivalence | Use de Bruijn indices or nominals |
| **Closure over wrong environment** | Wrong semantics for first-class functions | Deep copy or proper escaping |
| **Space leaks in closures** | Memory bloat in long-running programs | Implement thunks carefully |
| **Incorrect η-reduction** | Breaks observational equivalence | Disable or implement correctly |
| **Weak head normal form confusion** | Lazy vs eager semantics mixing | Choose strategy explicitly |
| **Infinite loops on diverging terms** | Non-termination without feedback | Add step limits, detect loops |

### The "Omega Combinator" Problem

The classic omega combinator `Ω = (λx. x x) (λx. x x)` diverges. Implementations must handle this:

```python
# Safe evaluation with step limiting
def eval_with_limit(term, env, max_steps=10000):
    for _ in range(max_steps):
        if is_value(term):
            return term
        term = step(term, env)
    raise RuntimeError("Non-termination detected")
```

### De Bruijn Index Pitfalls

When implementing de Bruijn indices, common bugs include:

1. **Index shifting during substitution**: `lift` must adjust indices correctly
2. **Capture in substitution**: Must check free variable sets
3. **Weak vs strong reduction**: Whether to reduce under lambdas

```python
# Correct de Bruijn substitution
def subst(term, index, replacement):
    match term:
        case DB(index') if index' == index:
            return replacement
        case DB(index') if index' > index:
            return DB(index' - 1)  # Shift down
        case Abs(body):
            return Abs(subst(body, index + 1, replacement.lift(1)))
        # ... more cases
```

## Connections to Real Systems

Lambda calculus implementations connect to major systems:

| Real System | Lambda Calculus Connection |
|-------------|---------------------------|
| **JavaScript V8** | Closures, scope chains trace to λ-calculus |
| **Python** | `lambda` is literal lambda calculus |
| **React hooks** | Closure semantics are core |
| **Functional languages** | All compile to variants of lambda calculus |
| **WebAssembly** | Function references are closure-like |

## Tradeoffs and Limitations

### Evaluation Strategy Tradeoffs

| Strategy | Pros | Cons |
|----------|------|------|
| **Call-by-Value (CBV)** | Efficient, matches eager languages | May duplicate work, diverges from math |
| **Call-by-Name (CBN)** | Simple, matches lazy languages | May duplicate thunks |
| **Call-by-Need** | Shares work, optimal for laziness | Complex implementation |
| **Parallel** | Fast on multicore | Nondeterministic results |

### When NOT to Use Pure λ-Calculus

- **For practical languages**: Add concrete syntax, recursion (Y combinator), constants
- **For performance-critical code**: Consider closure conversion, compilation to bytecode
- **For verification**: Use simply-typed or linear variants for stronger guarantees

### Limitations

- **Encoding overhead**: Natural numbers, booleans require Church encodings (inefficient)
- **No recursion**: Must use fixed-point combinator (Y = λf.(λx.f(x x))(λx.f(x x)))
- **α-equivalence**: Variables are not identical under renaming; requires care
- **Normalization**: Untyped λ-calculus is not strongly normalizing (may diverge)

## Assessment Criteria

A high-quality λ-calculus interpreter should have:

| Criterion | What to Look For |
|-----------|------------------|
| **Correctness** | Implements β-reduction correctly |
| **Efficiency** | Reasonable performance for typical terms |
| **Evaluation strategy** | Configurable CBV/CBN/need |
| **Error handling** | Clear errors for stuck terms |
| **Alpha equivalence** | Handles renaming correctly |
| **De Bruijn** | Correct index arithmetic |

### Quality Indicators

✅ **Good**: Correct β-reduction, handles closures, configurable strategies
⚠️ **Warning**: Missing η-reduction, inefficient environments
❌ **Bad**: Capture-avoidance bugs, infinite loops on normal terms
```
