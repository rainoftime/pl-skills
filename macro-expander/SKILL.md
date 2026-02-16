---
name: macro-expander
description: "Implement macro systems for syntactic abstraction and code generation at compile time."
version: "1.0.0"
tags: [metaprogramming, macros, pldi, lisp]
difficulty: intermediate
languages: [scheme, rust, julia]
dependencies: [parser-generator, lexer-generator]
---

# Macro Expander

Macro systems enable syntactic abstraction by transforming code at compile time. They allow programmers to extend the language with new syntactic constructs.

## When to Use This Skill

- Building DSLs (Domain-Specific Languages)
- Reducing boilerplate code
- Implementing language extensions
- Code generation
- Compile-time computation

## What This Skill Does

1. **Macro Definition**: Define syntax transformers
2. **Macro Expansion**: Transform macro calls into base syntax
3. **Hygiene**: Prevent unintended variable capture
4. **Pattern Matching**: Match macro input patterns
5. **Recursive Expansion**: Handle nested macros

## Key Concepts

| Concept | Description |
|---------|-------------|
| Macro | Syntax transformer |
| Hygiene | Prevents unintended variable capture |
| Pattern Variable | Placeholder in macro pattern |
| Expansion | Transform macro call to base syntax |
| Template | Output pattern for macro |

## Tips

- Use hygiene to prevent capture
- Prefer pattern-based macros for clarity
- Document macro contracts
- Test macro expansion thoroughly
- Consider compile-time errors

## Common Use Cases

- DSL implementation
- Boilerplate reduction
- Language extensions
- Conditional compilation
- Code generation

## Related Skills

- `parser-generator` - Macros need AST
- `dsl-embedding` - DSLs via macros
- `multi-stage-programming` - Staged computation

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| Kohlbecker et al. "Hygienic macro expansion" | Original hygiene paper |
| Dybvig et al. "Syntactic abstraction in Scheme" | Scheme macros |
| Rust macro documentation | Modern procedural macros |

## Tradeoffs and Limitations

### Approach Tradeoffs

| Approach | Pros | Cons |
|----------|------|------|
| Textual macros | Simple | Unhygienic |
| Hygienic macros | Safe | Complex |
| Procedural macros | Powerful | Hard to debug |

### When NOT to Use This Skill

- When functions suffice
- For simple syntactic sugar
- When debugging is important

### Limitations

- Hygiene is hard to get right
- Error messages can be cryptic
- Macro expansion can be slow

## Assessment Criteria

A high-quality implementation should have:

| Criterion | What to Look For |
|-----------|------------------|
| Hygiene | Prevents capture |
| Composability | Macros expand macros |
| Error handling | Clear error messages |
| Efficiency | Reasonable expansion time |

### Quality Indicators

✅ **Good**: Hygienic, pattern-based, good errors
⚠️ **Warning**: Sometimes captures variables
❌ **Bad**: Unhygienic, cryptic errors

## Research Tools & Artifacts

Real-world macro systems:

| Tool | Why It Matters |
|------|----------------|
| **Racket macros** | Advanced macro system |
| **Rust proc-macros** | Rust macro system |
| **C preprocessor** | Original textual macros |
| **Clang/LLVM** | Macro system for C |

### Key Systems

- **Racket**: Scheme macros
- **Julia macros**: Lisp-style macros

## Research Frontiers

Current macro research:

| Direction | Key Papers | Challenge |
|-----------|------------|-----------|
| ** hygiene** | "Hygienic Macros" | Sound hygiene |
| **Generative** | "Generative Macros" | Type generation |
| **Typed** | "Typed Macros" | Type-safe macros |

### Hot Topics

1. **Macro ML**: ML with macros
2. **Wasm macros**: WebAssembly macros

## Implementation Pitfalls

Common macro bugs:

| Pitfall | Real Example | Prevention |
|---------|--------------|------------|
| **Capture** | Variable capture | Hygiene |
| **Order** | Macro order | Phase separation |
