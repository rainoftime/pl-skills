---
name: algebraic-effects
description: "Implements algebraic effects and effect handlers for computational effects in typed languages."
version: "1.0.0"
tags: [effects, type-theory, semantics, handlers, monads]
difficulty: advanced
languages: [ocaml, haskell, eff, python]
dependencies: [effect-system, type-inference-engine]
---

# Algebraic Effects

Implements algebraic effects and effect handlers - a modular approach to computational effects where effects are described as operations and handled by handler functions.

## When to Use This Skill

- Building languages with composable effects
- Implementing async/await, state, exceptions, logging, nondeterminism
- Researching effect systems and handlers
- Creating domain-specific effect languages

## What This Skill Does

1. **Effect Signature Definition**: Defines effects as sets of operations with types
2. **Effect Handler Implementation**: Implements handlers that interpret effect operations
3. **Deep vs Shallow Handlers**: Supports both continuation-based deep handlers and single-shot shallow handlers
4. **Effect Inference**: Infers effect types from code using effect inference algorithms

## Key Concepts

| Concept | Description |
|---------|-------------|
| Effect Operation | Abstract description of an effect (e.g., `State.get`, `State.put`) |
| Effect Handler | Function that interprets effect operations |
| Resumption | Continuation passed to handler for resuming computation |
| Effect Row | Collection of effects tracked in type system |

## Tips

- Start with simple effects (state, exceptions)
- Use deep handlers for full resumption
- Consider effect inference to reduce annotation burden
- Handlers compose via delegation

## Related Skills

- `effect-system` - Effect type tracking
- `monad-transformer` - Alternative effect composition
- `type-inference-engine` - Effect inference

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| Eff: Programming with Algebraic Effects and Effect Handlers | Original Eff language papers |
| Algebraic Effects for Functional Programming | Practical handler implementation |
| Effect Handlers in Scope, Globally | Modular handler composition |

## Tradeoffs and Limitations

| Approach | Pros | Cons |
|----------|------|------|
| Deep handlers | Full resumption, composable | Complex continuation management |
| Shallow handlers | Simpler implementation | Limited expressiveness |
| Monadic encoding | Familiar, pure | Effets verbosity, lack of local reasoning |

## Assessment Criteria

| Criterion | What to Look For |
|-----------|------------------|
| Type safety | Effect operations well-typed |
| Handler correctness | Operations correctly interpreted |
| Performance | Minimal overhead vs monadic approach |
| Composability | Handlers can be layered |

### Quality Indicators

✅ **Good**: Type-safe, correct handlers, good performance, composable
⚠️ **Warning**: Partial type safety, some handler issues
❌ **Bad**: Type errors, incorrect handler behavior

## Research Tools & Artifacts

Algebraic effect implementations:

| Tool | Language | What to Learn |
|------|----------|---------------|
| **Eff** | OCaml | Original implementation |
| **Koka** | Koka | Effect types |
| **Frank** | Frank | Handler calculus |
| **Idris 2** | Idris | Effects |

## Research Frontiers

### 1. Effect Inference
- **Goal**: Reduce annotation burden
- **Papers**: "Effect Inference" (various)

## Implementation Pitfalls

| Pitfall | Real Consequence | Solution |
|---------|-----------------|----------|
| **Continuation leak** | Memory issues | Proper resumption |
