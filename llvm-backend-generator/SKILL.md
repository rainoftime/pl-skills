---
name: llvm-backend-generator
description: 'Generates LLVM IR and builds compilers targeting LLVM. Use when: (1)
  Building compilers, (2) Implementing language backends, (3) Creating optimization
  pipelines.'
version: 1.0.0
tags:
- compiler
- llvm
- code-generation
- backend
difficulty: intermediate
languages:
- python
- llvm
- c++
dependencies:
- ssa-constructor
---

# LLVM Backend Generator

Generates LLVM Intermediate Representation (IR) and builds compiler backends targeting LLVM.

## When to Use

- Building compilers for new languages
- Implementing language backends
- Creating optimization pipelines
- Generating native code
- Integrating with existing LLVM-based tools

## What This Skill Does

1. **Generates LLVM IR** - Creates valid LLVM bitcode
2. **Builds instruction selection** - Patterns for code generation
3. **Implements optimization passes** - Built-in and custom passes
4. **Handles ABI** - Calling conventions, data layout

## Key Concepts

| Concept | Description |
|---------|-------------|
| **LLVM IR** | Three-address code, SSA form |
| **Basic block** | Sequence of instructions, single entry/exit |
| **SSA** | Static Single Assignment - each variable assigned once |
| **Pass** | Transformation or analysis |
| **Target triple** | CPU/OS/platform combination |

## Optimization Pass Categories

| Category | Passes |
|----------|--------|
| **Analysis** | Dominators, loop info, alias analysis |
| **Transforms** | GVN, LICM, inlining, vectorization |
| **CodeGen** | Instruction selection, register allocation |

## Tips

- Use existing language frontends (Clang, Swift) as reference
- Implement proper name mangling for C++ interop
- Handle alignment and endianness correctly
- Use debug info metadata for debugging support
- Consider embedded languages (Emscripten, Rust)

## Related Skills

- `jit-compiler-builder` - JIT with LLVM ORC
- `ssa-constructor` - SSA form construction
- `type-checker-generator` - Type checking frontend
- `dataflow-analysis-framework` - Analysis passes

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| **Lattner & Adve, "LLVM: A Compilation Framework for Lifelong Program Analysis & Transformation" (CGO 2004)** | LLVM design |
| **The LLVM Language Reference** | IR specification |
| **LLVM Documentation** | Official docs and tutorials |
| **Kaleidoscope Tutorial** | Building a language with LLVM |

## Tradeoffs and Limitations

### Approaches

| Approach | Pros | Cons |
|----------|------|------|
| **Use LLVM API** | Full control, optimized | Complex API |
| **Use MCJIT/ORC** | Easier JIT | Less control |
| **Emit textual IR** | Simple, debuggable | Slower |

### Limitations

- Complex API learning curve
- Generated code quality depends on patterns
- Limited portability without target description
- Some targets less mature than x86/AArch64

## Research Tools & Artifacts

LLVM-based compilers:

| Tool | What to Learn |
|------|---------------|
| **Clang** | C/C++ frontend |
| **Rust** | Rust compiler |
| **Swift** | Swift compiler |

## Research Frontiers

### 1. WASM Compilation
- **Goal**: WebAssembly targets

## Implementation Pitfalls

| Pitfall | Real Consequence | Solution |
|---------|-----------------|----------|
| **Target bugs** | Wrong code | Test extensively |
