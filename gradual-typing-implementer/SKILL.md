---
name: gradual-typing-implementer
description: 'Implements gradual typing for dynamically-typed languages. Use when:
  (1) Adding type checking to dynamic languages, (2) Supporting migration to static
  types, (3) Hybrid type systems.'
version: 1.0.0
tags:
- type-systems
- gradual-typing
- dynamic-typing
- hybrid
difficulty: advanced
languages:
- python
- racket
- typescript
dependencies:
- type-checker-generator
---

# Gradual Typing Implementer

Implements gradual typing systems that bridge static and dynamic typing.

## When to Use

- Adding type checking to dynamic languages
- Supporting migration to static types
- Building hybrid type systems
- Implementing TypeScript-like systems
- Creating typed dialects of Python/Ruby

## What This Skill Does

1. **Defines gradual types** - Static + dynamic + ? types
2. **Implements type checking** - Consistent with gradual guarantee
3. **Handles casts** - Runtime type checks
4. **Manages errors** - Type mismatch reporting

## Key Concepts

| Concept | Description |
|---------|-------------|
| **Gradual guarantee** | Adding static types doesn't change behavior |
| **Consistent-with** | Flexible type matching (★) |
| **Unknown type** | Explicitly unknown ('?') |
| **Type precision** | Dynamic < Unknown < Static |

## The ★ Relation

| Type A | Type B | A consistent B? |
|--------|--------|-----------------|
| int | int | ✓ |
| int | dynamic | ✓ |
| dynamic | int | ✓ |
| int | string | ✗ |
| (int → int) | (dynamic → int) | ✓ |

## Tips

- Start with simple gradual system
- Use "any" as bottom for gradual
- Preserve dynamic behavior
- Good error messages are crucial
- Test with mixed static/dynamic code

## Related Skills

- `type-checker-generator` - Static type checking
- `type-inference-engine` - Type inference
- `refinement-type-checker` - Refinement types

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| **Siek & Taha, "Gradual Typing for Functional Languages" (2006)** | Original gradual typing |
| **Siek et al., "Gradual Typing in Practice"** | Practical gradual typing |
| **TypeScript Language Specification** | Production gradual typing |
| **Typed Racket** | Gradual typing in practice |

## Tradeoffs and Limitations

### Design Tradeoffs

| Approach | Pros | Cons |
|----------|------|------|
| **Erasure** | Simple, fast | Runtime overhead |
| **Reified** | Type info at runtime | Memory |
| **Blame** | Clear error responsibility | Complexity |

### Limitations

- Runtime overhead for checks
- Cannot fully verify static properties
- Type inference is harder
- Error messages can be confusing
- Performance tuning is complex

## Research Tools & Artifacts

Gradual typing in practice:

| Tool | Language | What to Learn |
|------|----------|---------------|
| **TypeScript** | JavaScript | Production gradual |
| **Typed Racket** | Racket | Academic |
| **Pyright** | Python | Gradual |

## Research Frontiers

### 1. Blame Tracking
- **Goal**: Error localization

## Implementation Pitfalls

| Pitfall | Real Consequence | Solution |
|---------|-----------------|----------|
| **Runtime overhead** | Slow checks | Optimize |
