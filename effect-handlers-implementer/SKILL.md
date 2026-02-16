---
name: effect-handlers-implementer
description: 'Implements effect handlers for algebraic effects. Use when: (1) Building
  effect systems, (2) Implementing custom effects, (3) Creating extensible effects.'
version: 1.0.0
tags:
- effects
- handlers
- control-flow
- algebraic-effects
difficulty: advanced
languages:
- python
- haskell
- ocaml
dependencies:
- effect-type-system
---

# Effect Handlers Implementer

Implements effect handlers for algebraic effects and resumable exceptions.

## When to Use

- Building effect systems
- Implementing custom effects (I/O, state, nondeterminism)
- Creating extensible effect systems
- Implementing error handling
- Building async/await with effects

## What This Skill Does

1. **Defines effects** - Algebraic effect signatures
2. **Implements handlers** - Effect interpretation
3. **Manages continuations** - Resumable computations
4. **Composes handlers** - Layered interpretations

## Key Concepts

| Concept | Description |
|---------|-------------|
| **Effect** | Operation signature (type of operations) |
| **Handler** | Interpretation of effects |
| **Continuation** | Remaining computation |
| **Resumption** | Continue after handling |
| **Abort** | Stop computation |

## Common Effects

| Effect | Operations | Handler |
|--------|------------|---------|
| **State** | get, put | StateHandler |
| **Exceptions** | throw, catch | FailHandler |
| **I/O** | read, write | IOHandler |
| **Non-det** | choose, fail | ChoiceHandler |
| **Random** | random | RandomHandler |
| **Async** | async, await | AsyncHandler |

## Handler Composition

| Pattern | Description |
|---------|-------------|
| **Shallow** | One-shot handling |
| **Deep** | Intercept nested effects |
| **Scoped** | Dynamic handler scope |
| **Layered** | Multiple handlers |

## Tips

- Start with simple effects (state, fail)
- Use effect rows for polymorphism
- Handle resource cleanup with finally
- Test handlers in isolation
- Consider performance of continuations

## Related Skills

- `effect-type-system` - Effect type systems
- `polymorphic-effects` - Effect polymorphism
- `lambda-calculus-interpreter` - Basic interpretation

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| **Plotkin & Pretnar, "Handlers of Algebraic Effects" (2009)** | Original effect handlers |
| **Koka Language** | Production effect system |
| **Eff Language** | Research effect language |
| **Frank Language** | Effect handlers in practice |

## Tradeoffs and Limitations

### Approaches

| Approach | Pros | Cons |
|----------|------|------|
| **Monadic** | Simple, composable | Verbose |
| **Effect handlers** | Extensible, modular | Complex implementation |
| **Delimited continuations** | Powerful | Hard to use |

### Limitations

- Performance overhead for continuations
- Complex to implement correctly
- Debugging is challenging
- Limited static analysis
- Some effects can't be handler

## Research Tools & Artifacts

Real-world effect handler implementations:

| Tool | Why It Matters |
|------|----------------|
| **Koka** | Production language with effect types |
| **Frank** | Effect handlers research language |
| **Eff** | Effect handlers implementation |
| **OCaml effects** | Experimental effects in OCaml |
| **Multicore OCaml** | Effect handlers for OCaml |

### Key Systems

- **Koka**: Microsoft research effect language
- **Frank**: Chameleon in the forest

## Research Frontiers

Current effect handler research:

| Direction | Key Papers | Challenge |
|-----------|------------|-----------|
| **Typed handlers** | "Handlers of Algebraic Effects" | Type-safe handlers |
| **Continuations** | "Delimited Control" | Efficient continuations |
| **Effect polymorphism** | "Polymorphic Effects" | Reusable handlers |

### Hot Topics

1. **Effect handlers for web**: Async via handlers
2. **Effects in Rust**: Effects RFC discussion

## Implementation Pitfalls

Common effect handler bugs:

| Pitfall | Real Example | Prevention |
|---------|--------------|------------|
| **Resume after abort** | Double resume | Track state |
| **Stack overflow** | Deep continuations | Tail-call opt |
| **Handler order** | Wrong handler catches | Order matters |
