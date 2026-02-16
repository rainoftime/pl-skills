---
name: mlir-dialect-designer
description: 'Designs MLIR dialects and transformations. Use when: (1) Building domain-specific
  compilers, (2) Creating IR abstractions, (3) Implementing multi-level lowering.'
version: 1.0.0
tags:
- compiler
- mlir
- dialects
- llvm
difficulty: advanced
languages:
- c++
- mlir
dependencies:
- llvm-backend-generator
---

# MLIR Dialect Designer

Designs MLIR (Multi-Level Intermediate Representation) dialects and transformations.

## When to Use

- Building domain-specific compilers
- Creating custom IR abstractions
- Implementing multi-level lowering
- Optimizing compilers for specific domains
- Integrating with LLVM ecosystem

## What This Skill Does

1. **Designs dialects** - Custom operations and types
2. **Defines patterns** - Transformation rules
3. **Implements lowering** - Dialect-to-dialect lowering
4. **Creates passes** - Optimization and lowering passes

## Key Concepts

| Concept | Description |
|---------|-------------|
| **Dialect** | Collection of operations and types |
| **Operation** | Instructions in the IR |
| **Block** | Sequence of operations |
| **Region** | Container for blocks |
| **Pattern** | Transformation rule |

## Standard Dialects

| Dialect | Purpose |
|---------|---------|
| **arith** | Arithmetic operations |
| **linalg** | Linear algebra |
| **affine** | Affine loops/conditionals |
| **scf** | Structured control flow |
| **func** | Function definitions |
| **LLVM** | LLVM dialect |

## Tips

- Design operations at right abstraction level
- Use traits for common operation properties
- Implement folding for constant propagation
- Follow ODS (Operation Definition Specification)
- Test patterns thoroughly

## Related Skills

- `llvm-backend-generator` - LLVM code generation
- `ssa-constructor` - SSA form
- `dataflow-analysis-framework` - Analysis
- `llvm-backend-generator` - Integration

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| **MLIR Specification** | Official MLIR docs |
| **TensorFlow MLIR** | Production MLIR usage |
| **LLVM Developers Meeting Talks** | MLIR design talks |
| **ODSv2 Tutorial** | Operation definition |

## Tradeoffs and Limitations

### Design Tradeoffs

| Approach | Pros | Cons |
|----------|------|------|
| **High-level ops** | Simple, easy to optimize | Less control |
| **Low-level ops** | Fine-grained control | Complex patterns |
| **Hybrid** | Balance | Complexity |

### Limitations

- Steep learning curve
- Large ecosystem to understand
- Patterns can be complex
- Dialect conversion requires care

## Research Tools & Artifacts

Real-world MLIR dialects:

| Tool | Why It Matters |
|------|----------------|
| **Linalg** | Linear algebra dialect |
| **SCF** | Control flow dialect |
| **Affine** | Affine loops dialect |
| **Vector** | Vector operations |

### Key Systems

- **TensorFlow MLIR**: Production MLIR
- **IREE**: MLIR-based runtime

## Research Frontiers

Current MLIR research:

| Direction | Key Papers | Challenge |
|-----------|------------|-----------|
| **Dialect design** | "MLIR Design" | Abstractions |
| **Lowering** | "Dialect Lowering" | Patterns |

### Hot Topics

1. **Wasm MLIR**: WebAssembly dialect
2. **Quantum MLIR**: Quantum dialects

## Implementation Pitfalls

Common MLIR bugs:

| Pitfall | Real Example | Prevention |
|---------|--------------|------------|
| **Patterns** | Wrong pattern | Test |
