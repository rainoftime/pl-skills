---
name: type-class-implementer
description: "Implement type classes for ad-hoc polymorphism and overloading in programming languages."
version: "1.0.0"
tags: [type-theory, polymorphism, haskell, pldi]
difficulty: intermediate
languages: [haskell, rust, scala]
dependencies: [type-inference-engine]
---

# Type Class Implementer

Type classes provide a structured way to add ad-hoc polymorphism to a language, allowing functions to operate on different types while maintaining type safety. Originally introduced in Haskell, they're now used in Rust (traits), Scala (implicits), and other languages.

## When to Use This Skill

- Implementing overloaded operations (equality, ordering, printing)
- Building generic libraries that work across types
- Creating extensible abstractions
- Implementing type-directed program synthesis
- Building effect systems (monads, functors)

## What This Skill Does

1. **Class Declaration**: Define a set of operations with type signatures
2. **Instance Declaration**: Provide implementations for specific types
3. **Constraint Propagation**: Track type class constraints during inference
4. **Dictionary Passing**: Implement runtime representation of instances
5. **Coherence Resolution**: Resolve overlapping instances deterministically

## Key Concepts

| Concept | Description |
|---------|-------------|
| Class | Collection of method signatures |
| Instance | Implementation of a class for a type |
| Constraint | Requirement that a type has an instance |
| Dictionary | Runtime representation of an instance |
| Coherence | Each type has at most one instance per class |
| Superclass | Class that must be satisfied before another |

## Tips

- Use dictionary passing for simple implementations
- Implement instance search as constraint solving
- Consider orphan instances carefully for modularity
- Use default methods to reduce boilerplate
- Implement functional dependencies for multi-parameter classes

## Common Use Cases

- Implementing Eq, Ord, Show for standard types
- Building Monad, Functor hierarchies
- Creating numeric type classes (Num, Fractional)
- Implementing serialization/deserialization
- Building effect systems

## Related Skills

- `type-inference-engine` - Hindley-Milner with type classes
- `system-f` - Alternative polymorphism mechanism
- `trait-system` - Rust's approach to type classes
- `module-system` - ML modules as alternative

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| Wadler, Blott "How to make ad-hoc polymorphism less ad hoc" (1989) | Original type classes paper |
| Jones "Type classes with functional dependencies" | Multi-parameter type classes |
| GHC User's Guide "Type classes" | Practical implementation |

## Tradeoffs and Limitations

### Approach Tradeoffs

| Approach | Pros | Cons |
|----------|------|------|
| Dictionary passing | Simple, explicit | Verbose, manual threading |
| Implicit passing | Clean syntax | Hidden runtime cost |
| Trait objects (Rust) | Dynamic dispatch | Runtime overhead |

### When NOT to Use This Skill

- When simple function overloading suffices
- For performance-critical inner loops
- When module system provides enough abstraction

### Limitations

- Coherence can limit modularity
- Orphan instances cause problems
- Multi-parameter classes need extensions

## Assessment Criteria

A high-quality implementation should have:

| Criterion | What to Look For |
|-----------|------------------|
| Coherence | Each type has at most one instance |
| Constraint Simplification | Solves constraints during inference |
| Default Methods | Supports default implementations |
| Error Messages | Clear indication of missing instances |

### Quality Indicators

✅ **Good**: Coherent instances, good error messages, supports default methods
⚠️ **Warning**: Overlapping instances without resolution strategy
❌ **Bad**: No coherence checking, silent instance shadowing

## Research Tools & Artifacts

Type class systems:

| Tool | Language | What to Learn |
|------|----------|---------------|
| **Haskell** | Haskell | Original |
| **GHC** | Haskell | Advanced features |
| **Rust traits** | Rust | Different approach |

## Research Frontiers

### 1. Qualified Types
- **Approach**: Typeclass-like overloading

## Implementation Pitfalls

| Pitfall | Real Consequence | Solution |
|---------|-----------------|----------|
| **Orphan instances** | Coherence issues | Avoid orphans |
