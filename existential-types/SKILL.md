---
name: existential-types
description: "Implement existential types for data abstraction and hiding type information."
version: "1.0.0"
tags: [type-theory, abstraction, haskell, popl]
difficulty: intermediate
languages: [haskell, ocaml, rust]
dependencies: [system-f, type-checker-generator]
---

# Existential Types

Existential types (∃α.τ) hide a type variable within a type, enabling data abstraction and the creation of heterogeneous collections. They are the dual of universal types (∀α.τ) in System F.

## When to Use This Skill

- Implementing abstract data types (ADTs)
- Creating heterogeneous collections
- Building type-erased interfaces
- Implementing dynamic dispatch patterns
- Hiding implementation details

## What This Skill Does

1. **Existential Quantification**: Hide type variables in data types
2. **Type Abstraction**: Expose operations without revealing implementation type
3. **Witness Types**: Package a type with operations on that type
4. **Type Erasure**: Remove type information at boundaries
5. **Dynamic Typing**: Recover type information when needed

## Key Concepts

| Concept | Description |
|---------|-------------|
| Existential Quantification | ∃α.τ - there exists some type α such that τ |
| Type Hiding | Internal type not exposed to external observers |
| Package | Value bundled with operations |
| Abstract Type | Type known only by its operations |
| Dual of Universal | ∃α.τ ≈ ∀β.(∀α.τ→β)→β |

## Tips

- Use GADTs for existential types in Haskell
- Existentials correspond to interfaces/protocols in OOP
- Think of them as "some type T, we don't know which"
- Combine with type classes for operation bundles
- Use continuation-passing for rank-2 types

## Common Use Cases

- Abstract data types (stacks, queues, maps)
- Type-erased callbacks and handlers
- Heterogeneous collections
- State machines with hidden state
- Effect handlers

## Related Skills

- `system-f` - Universal quantification (∀)
- `gadt-implementer` - GADTs for existentials
- `module-system` - ML modules for abstraction
- `type-class-implementer` - Type classes for operations

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| Mitchell, Plotkin "Abstract types have existential type" (1988) | Classic paper |
| Pierce "Types and Programming Languages" Ch. 24 | Textbook treatment |
| GHC User's Guide "ExistentialQuantification" | Practical usage |

## Tradeoffs and Limitations

### Approach Tradeoffs

| Approach | Pros | Cons |
|----------|------|------|
| GADT syntax | Clean, integrated | GHC specific |
| Explicit forall | Standard Haskell | More verbose |
| newtype wrapper | Simple | Limited flexibility |

### When NOT to Use This Skill

- When concrete types are known (use direct types)
- For simple polymorphism (use `system-f`)
- When performance is critical (boxing overhead)

### Limitations

- Cannot pattern match on hidden type
- Some runtime overhead for packaging
- Type inference is limited

## Assessment Criteria

A high-quality implementation should have:

| Criterion | What to Look For |
|-----------|------------------|
| Type Safety | Hidden type cannot escape its scope |
| Abstraction | Implementation details are hidden |
| Operations | Packaged with necessary operations |
| Composition | Can combine existential packages |

### Quality Indicators

✅ **Good**: Clean abstraction, well-defined operations, type-safe interface
⚠️ **Warning**: Escapes existential scope, exposes hidden type
❌ **Bad**: No real abstraction, just wrapping values

## Research Tools & Artifacts

Existential types in:

| Tool | Language | What to Learn |
|------|----------|---------------|
| **GHC** | Haskell | Implementation |
| **OCaml** | OCaml | Objects |

## Research Frontiers

### 1. Dynamic Types
- **Approach**: Type erasure

## Implementation Pitfalls

| Pitfall | Real Consequence | Solution |
|---------|-----------------|----------|
| **Type escape** | Violates abstraction | Scope tracking |
