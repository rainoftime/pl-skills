---
name: webassembly-runtime
description: 'Implements WebAssembly runtimes and execution engines. Use when: (1)
  Building WASM runtimes, (2) Implementing language compilers to WASM, (3) Creating
  WASM tooling.'
version: 1.0.0
tags:
- runtime
- webassembly
- wasm
- execution
difficulty: intermediate
languages:
- rust
- c++
dependencies:
- webassembly-verifier
---

# WebAssembly Runtime

Implements WebAssembly (WASM) execution engines and runtime systems.

## When to Use

- Building WASM runtimes for new languages
- Implementing compilers that target WASM
- Creating WASM tooling (debuggers, profilers)
- Building serverless/edge computing platforms
- Implementing WASM sandbox environments

## What This Skill Does

1. **Parses WASM binary format** - Decodes module structure
2. **Implements instruction set** - Executes WASM operations
3. **Manages memory** - Linear memory and tables
4. **Handles calls** - Function calls, indirect calls, host calls

## Key Concepts

| Concept | Description |
|---------|-------------|
| **Linear memory** | Contiguous byte array, page-granular |
| **Function indices** | Direct and indirect calls |
| **Table** | Function pointers for indirect calls |
| **Module instance** | Runtime representation |
| **Stack machine** | WASM uses operand stack |

## WASM Specification Highlights

| Feature | Details |
|---------|---------|
| **Types** | i32, i64, f32, f64, v128 |
| **Memory** | Up to 2^16 pages (4GB max) |
| **Functions** | Typed, can trap |
| **Control** | Structured (blocks, loops, if) |
| **Calls** | Direct, indirect, host |
| **Traps** | Unrecoverable errors |

## Tips

- Use lazy instantiation for modules
- Implement bounds checking efficiently
- Consider JIT compilation for performance
- Handle WebAssembly System Interface (WASI) for syscalls
- Support both binary and text formats

## Related Skills

- `jit-compiler-builder` - JIT compilation techniques
- `parser-generator` - Parse WASM binary/text
- `garbage-collector-implementer` - Memory management
- `webassembly-runtime` - Safe execution environment

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| **WebAssembly Specification (2024)** | Official spec for WASM core |
| **Haas et al., "Bringing the Web up to Speed with WebAssembly" (PLDI 2017)** | WASM design rationale |
| **WASI Specification** | System interface for WASM |
| **Wasmtime Implementation** | Production WASM runtime |

## Tradeoffs and Limitations

### Implementation Approaches

| Approach | Pros | Cons |
|----------|------|------|
| **Interpreter** | Simple, portable | Slow |
| **JIT** | Fast | Complex |
| **AOT** | Fastest | Limited portability |

### Limitations

- No garbage collection in core spec (coming in GC proposal)
- No threads in core spec (threads proposal available)
- Limited syscall access (WASI helps)
- Sandboxing requires careful design

## Research Tools & Artifacts

WASM runtimes:

| Tool | What to Learn |
|------|---------------|
| **Wasmtime** | Fast runtime |
| **WAVM** | LLVM-based |
| **Wasmer** | Multi-backend |

## Research Frontiers

### 1. GC Proposal
- **Goal**: Garbage collection in WASM

## Implementation Pitfalls

| Pitfall | Real Consequence | Solution |
|---------|-----------------|----------|
| **Bounds checks** | Security | Efficient checks |
