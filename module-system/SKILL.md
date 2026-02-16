---
name: module-system
description: "Implement module systems for organizing code, encapsulation, and namespace management."
version: "1.0.0"
tags: [runtime, modules, pldi, design]
difficulty: intermediate
languages: [ocaml, haskell, rust]
dependencies: [type-checker-generator]
---

# Module System

Module systems provide mechanisms for organizing code, encapsulating implementation details, and managing namespaces. They are essential for building large-scale software systems.

## When to Use This Skill

- Designing language module systems
- Building large codebases
- Implementing encapsulation
- Managing dependencies
- Teaching programming language design

## What This Skill Does

1. **Namespace Management**: Organize names into hierarchical namespaces
2. **Encapsulation**: Hide implementation details
3. **Interface/Implementation Separation**: Define signatures and structures
4. **Functors/Parameterized Modules**: Create module-level functions
5. **Dependency Management**: Handle module dependencies

## Key Concepts

| Concept | Description |
|---------|-------------|
| Module | Collection of related definitions |
| Signature | Module interface specification |
| Structure | Module implementation |
| Functor | Module-level function |
| Sealing | Hide implementation behind signature |
| Import | Use definitions from another module |

## Tips

- Use signatures for abstraction
- Seal modules to hide implementation
- Use functors for generic libraries
- Consider cyclic dependencies carefully
- Separate interface from implementation

## Common Use Cases

- Large-scale software organization
- Library design
- Namespace management
- Information hiding
- Dependency injection via functors

## Related Skills

- `type-class-implementer` - Alternative abstraction mechanism
- `ffi-designer` - Foreign function interface
- `type-checker-generator` - Type checking for modules

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| MacQueen "Modules for Standard ML" | Original ML modules |
| Leroy "Manifest types, modules, and separate compilation" | OCaml modules |
| Dreyer "Understanding and Evolving ML Modules" | Modern treatment |

## Tradeoffs and Limitations

### Approach Tradeoffs

| Approach | Pros | Cons |
|----------|------|------|
| Simple modules | Easy to implement | Limited abstraction |
| ML-style | Powerful abstraction | Complex |
| Mixins/Traits | Composable | No sealing |

### When NOT to Use This Skill

- Small single-file programs
- When simple imports suffice
- Prototype/experimental code

### Limitations

- Cyclic dependencies are tricky
- Higher-order modules are complex
- Type abstraction can be limited

## Assessment Criteria

A high-quality implementation should have:

| Criterion | What to Look For |
|-----------|------------------|
| Encapsulation | Hides implementation |
| Namespace | Manages names properly |
| Dependencies | Handles imports correctly |
| Abstraction | Supports signatures |

### Quality Indicators

✅ **Good**: Full encapsulation, proper namespacing, functor support
⚠️ **Warning**: Leaky abstraction, complex dependency handling
❌ **Bad**: No encapsulation, namespace pollution

## Research Tools & Artifacts

Real-world module systems:

| Tool | Why It Matters |
|------|----------------|
| **OCaml modules** | Full-featured modules |
| **ML signatures** | ML module system |
| **Rust modules** | Simple module system |
| **Java modules (JDK 9)** | Java module system |

### Key Systems

- **GHC Haskell**: Type-based modules
- **Dune**: OCaml build system

## Research Frontiers

Current module research:

| Direction | Key Papers | Challenge |
|-----------|------------|-----------|
| **Hierarchical** | "Hierarchical Modules" | Scale |
| **Mixins** | "Mixins" | Composition |
| **Types** | "Modules as Types" | Type-based |

### Hot Topics

1. **Wasm modules**: WebAssembly modules
2. **ES modules**: JavaScript modules

## Implementation Pitfalls

Common module bugs:

| Pitfall | Real Example | Prevention |
|---------|--------------|------------|
| **Cyclic deps** | Circular imports | Detect cycles |
| **Name collision** | Name conflicts | Namespaces |
