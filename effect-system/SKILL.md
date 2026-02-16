---
name: effect-system
description: "Implement effect systems to track and control side effects in programs."
version: "1.0.0"
tags: [effects, types, purity, popl]
difficulty: intermediate
languages: [haskell, purecript, koka]
dependencies: [type-checker-generator, type-class-implementer]
---

# Effect System

Effect systems track what computational effects a function may perform, enabling reasoning about purity, exceptions, I/O, and other side effects at the type level.

## When to Use This Skill

- Building pure functional languages
- Reasoning about side effects
- Implementing effect handlers
- Security and sandboxing
- Optimization (pure code can be optimized more)

## What This Skill Does

1. **Effect Annotation**: Track effects in types
2. **Effect Checking**: Verify effect constraints
3. **Effect Polymorphism**: Generic effect handling
4. **Effect Row Types**: Combine multiple effects
5. **Effect Masking**: Hide effects from callers

## Key Concepts

| Concept | Description |
|---------|-------------|
| Effect | Computational side effect (IO, State, Throw) |
| Effect Set | Collection of effects |
| Effect Row | Extensible row of effects |
| Effect Polymorphism | Generic over effect sets |
| Effect Handler | Interpret effects |
| Pure | No effects |

## Tips

- Start with coarse-grained effects (IO vs Pure)
- Use row polymorphism for flexibility
- Consider effect subtyping
- Effect handlers enable flexible interpretation
- Log effects for debugging

## Common Use Cases

- Pure functional languages
- Effect tracking for optimization
- Sandboxing and security
- Effect-based testing
- Resource management

## Related Skills

- `algebraic-effects` - Algebraic effect handlers
- `type-class-implementer` - Monad type classes
- `monad-transformer` - Monad transformers
- `information-flow-analyzer` - Security effects

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| Lucassen, Gifford "Polymorphic Effect Systems" | Original paper |
| Talpin, Jouvelot "The Type and Effect Discipline" | Effect polymorphism |
| Koka language documentation | Modern effect system |

## Tradeoffs and Limitations

### Approach Tradeoffs

| Approach | Pros | Cons |
|----------|------|------|
| Monads | Composable | Syntactic overhead |
| Effect systems | Cleaner syntax | Complex inference |
| Algebraic effects | Flexible | Runtime overhead |

### When NOT to Use This Skill

- When side effects are not a concern
- Performance-critical code
- When exceptions suffice

### Limitations

- Effect inference can be complex
- Higher-order effects are tricky
- Interaction with existing code

## Assessment Criteria

A high-quality implementation should have:

| Criterion | What to Look For |
|-----------|------------------|
| Soundness | All effects tracked |
| Inference | Automatic effect inference |
| Polymorphism | Effect polymorphism |
| Handlers | Effect interpretation |

### Quality Indicators

✅ **Good**: Sound, infers effects, supports polymorphism
⚠️ **Warning**: Manual annotations required
❌ **Bad**: Misses effects, no polymorphism

## Research Tools & Artifacts

Effect system implementations:

| Tool | Language | What to Learn |
|------|----------|---------------|
| **Koka** | Koka | Row-based effects |
| **Frank** | Frank | Handler calculus |
| **Eff** | Eff | Direct handlers |
| **Multicore OCaml** | OCaml | Effects in OCaml |

## Research Frontiers

### 1. Effect Inference
- **Goal**: Automatic effect tracking
- **Papers**: "Effect Inference" (various)

## Implementation Pitfalls

| Pitfall | Real Consequence | Solution |
|---------|-----------------|----------|
| **Effect inference** | Complexity | Use bidirectional |
