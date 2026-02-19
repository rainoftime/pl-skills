---
name: closure-converter
description: 'Transforms closures to explicit environments. Use when: (1) Implementing
  functional languages, (2) Building compilers, (3) Understanding closures.'
version: 1.0.0
tags:
- compiler
- closures
- code-generation
- functional
difficulty: intermediate
languages:
- python
- ocaml
- rust
dependencies:
- lambda-calculus-interpreter
---

# Closure Converter

Transforms closures to explicit environment passing.

## When to Use

- Implementing functional language compilers
- Building interpreters
- Understanding closure semantics
- Transforming functional to imperative

## What This Skill Does

1. **Analyzes free variables** - Determines captured variables
2. **Creates closures** - Transforms lambdas
3. **Passes environments** - Explicit env parameter
4. **Optimizes** - Avoids unnecessary captures

## Key Concepts

| Concept | Description |
|---------|-------------|
| **Free variables** | Variables used but not defined |
| **Closure** | Function + captured environment |
| **Environment** | Mapping from variables to values |
| **Lambda lifting** | Move functions to top level |

## Techniques

- Flat environments
- Shared closures
- Lambda lifting
- Representation analysis

## Tips

- Track free variables precisely
- Consider environment representation
- Handle recursive functions
- Optimize shared closures

## Related Skills

- `lambda-calculus-interpreter` - Lambda calculus
- `jit-compiler-builder` - VM design
- `lambda-calculus-interpreter` - Bytecode

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| **Reynolds, "Definitional Interpreters for Higher-Order Functions" (1972)** | Closure conversion theory |
| **Plotkin, "Call-by-Name, Call-by-Value and the λ-Calculus" (1975)** | Lambda calculus foundations |
| **Fisher & Springer, "Lambda-Liftable Modules" (2000)** | Lambda lifting and closure conversion |

## Research Tools & Artifacts

Real-world closure conversion implementations to study:

| Artifact | Why It Matters |
|----------|----------------|
| **GHC's closure analysis** | Sophisticated info table and closure representation |
| **OCaml's closure conversion** | Production-quality, optimized for performance |
| **Scala 2 lambda encoding** | Anonymous function representation |
| **LuaJIT's closure IR** | Trace-based closure optimization |
| **PyPy's closure conversion** | Tracing JIT with efficient closures |
| **V8's closure representation** | Hidden class and context optimization |

### Key Compiler Implementations

- **GHC via STG**: Top-level thunks, updatable frames
- **Clean**: Graph rewriting with unique nodes, I/O requirements and uniqueness types

## Research Frontiers

Current active research in closure conversion:

| Direction | Key Papers | Challenge |
|-----------|------------|-----------|
| **Zero-cost closures** | "Zero-cost Closures" (2018) | No heap allocation for non-escaping |
| **In-place updates** | "Thunks revisited" (2008) | Update-in-place vs copying |
| **Unboxed representations** | "Unboxed tuples" (GHC) | Avoiding heap allocation |
| **Escape analysis** | "Escape Analysis" (1994) | Static lifetime detection |
| **Lambda lifting** | "Lambda dropping" (2001) | When to lift, what to capture |

### Hot Topics

1. **Swift's escaping closures**: Distinguishing escaping vs non-escaping
2. **Rust's closure traits**: Fn, FnMut, FnOnce with capture semantics
3. **Wasm GC proposal**: First-class function references

## Implementation Pitfalls

Common bugs in production closure conversion:

| Pitfall | Real Example | Prevention |
|---------|--------------|------------|
| **Wrong free variable set** | Early Scala lost captured vars | Compute FV with bound variable hygiene |
| **Space leaks** | GHC's CAFs holding closures | Analyze thunk vs value carefully |
| **Lambda lift too early** | Lost sharing opportunities | Lift after inlining |
| **Wrong environment order** | Variable capture bugs | Verify env layout matches usage |
| **Closure escape** | JavaScript hidden class changes | Track escape precisely |
| **Mutable capture** | Closure capturing mutref unsoundness | Track mutability separately |

### The "Mutable Capture" Bug

In languages with mutability:
```scala
// Unsound if closure captures mutable ref
val x = Ref(0)
val f = () => { x := 1; x() }
```

**Solution**: Mark closures that capture mutable references, restrict their usage.

### Lambda Lifting Tradeoffs

Lambda lifting too early loses optimization opportunities:
- Lift after inlining to see usage patterns
- Consider partial application patterns
- Don't lift if closure escapes current scope
