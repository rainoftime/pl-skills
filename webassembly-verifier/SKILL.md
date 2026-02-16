---
name: webassembly-verifier
description: 'Verifies WebAssembly modules for safety and correctness. Use when: (1)
  Validating WASM modules, (2) Building security tools, (3) Implementing sandboxes.'
version: 1.0.0
tags:
- verification
- webassembly
- bytecode
- sandboxing
difficulty: intermediate
languages:
- python
- rust
dependencies: []
---

# WebAssembly Verifier

Verifies WebAssembly modules for safety, security, and correctness properties.

## When to Use

- Validating untrusted WASM modules
- Building WASM security tools
- Implementing sandboxes
- Verifying memory safety
- Proving absence of runtime errors

## What This Skill Does

1. **Type checks modules** - Validates type correctness
2. **Verifies stack** - Balanced push/pop operations
3. **Checks bounds** - Memory access safety
4. **Validates control flow** - Structured execution

## Key Concepts

| Concept | Description |
|---------|-------------|
| **Type use** | Function type references |
| **Block type** | Control flow return type |
| **Stack polymorphism** | Dynamic stack height |
| **Validation context** | Current type environment |

## Validation Rules

| Category | Checks |
|----------|--------|
| **Type use** | Index in bounds |
| **Function** | Locals, return type |
| **Stack** | Balanced pushes/pops |
| **Control** | Proper label nesting |
| **Memory** | Bounds, alignment |

## Tips

- Implement incrementally by instruction class
- Track stack height precisely
- Handle unreachable code properly
- Verify at load time, not runtime
- Consider symbolic verification

## Related Skills

- `webassembly-runtime` - WASM execution
- `model-checker` - Model checking
- `type-checker-generator` - Type checking
- `webassembly-runtime` - Safe execution

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| **WebAssembly Specification - Validation** | Official validation spec |
| **Haas et al., "Bringing the Web up to Speed with WebAssembly" (PLDI 2017)** | WASM design |
| **WebAssembly Binary Toolkit** | Validator tools |

## Tradeoffs and Limitations

### Approaches

| Approach | Pros | Cons |
|----------|------|------|
| **Syntactic validation** | Fast, complete | No semantic proofs |
| **Symbolic verification** | Deep properties | Slow, complex |
| **Runtime checks** | Dynamic safety | Performance cost |

### Limitations

- Cannot verify all runtime properties statically
- Cannot prove termination
- Limited introspection of data
- Validation is sound but not complete

## Research Tools & Artifacts

Real-world Wasm verification tools:

| Tool | Why It Matters |
|------|----------------|
| **wasm-validate** | Official validator |
| **WABT** | Tool suite |
| **wasm-micro-runtime** | Runtime |
| **V8** | JS engine with Wasm |

### Key Systems

- **W3C spec**: Standard
- **Firefox Wasm**: Production

## Research Frontiers

Current Wasm verification research:

| Direction | Key Papers | Challenge |
|-----------|------------|-----------|
| **Security** | "Wasm Security" | Isolation |
| **Verification** | "Verified Wasm" | Properties |

### Hot Topics

1. **Wasm GC**: Garbage collection
2. **Wasm WASI**: System interface

## Implementation Pitfalls

Common Wasm verification bugs:

| Pitfall | Real Example | Prevention |
|---------|--------------|------------|
| **Stack** | Stack underflow | Check |
