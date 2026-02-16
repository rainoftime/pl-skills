---
name: register-allocator
description: "Implement register allocation for mapping virtual registers to physical registers in compilers."
version: "1.0.0"
tags: [compilation, optimization, llvm, pldi]
difficulty: advanced
languages: [c++, rust, python]
dependencies: [ssa-constructor, liveness-analysis]
---

# Register Allocator

Register allocation maps an unlimited number of virtual registers (or temporaries) to a finite set of hardware registers. It is a critical optimization phase in compilers that directly impacts program performance.

## When to Use This Skill

- Building compiler backends
- Optimizing code generation
- Implementing JIT compilers
- Reducing memory traffic
- Working with SSA-form IR

## What This Skill Does

1. **Liveness Analysis**: Determine live ranges of variables
2. **Interference Graph**: Build graph of overlapping live ranges
3. **Graph Coloring**: Assign colors (registers) to nodes
4. **Spill Code**: Handle cases when registers are exhausted
5. **Coalescing**: Eliminate unnecessary register-to-register moves

## Key Concepts

| Concept | Description |
|---------|-------------|
| Live Range | Instructions where a variable holds a useful value |
| Interference | Two variables cannot share a register if live simultaneously |
| Spill | Store variable to memory when registers exhausted |
| Coalescing | Merge variables to eliminate moves |
| SSA Form | Simplifies allocation with phi functions |

## Tips

- Use SSA form to simplify liveness analysis
- Prefer linear scan for JIT compilers (faster)
- Use graph coloring for ahead-of-time compilers (better quality)
- Implement coalescing to reduce register-to-register moves
- Consider register hints for calling conventions

## Common Use Cases

- Compiler backend code generation
- JIT compiler optimization
- GPU shader compilers
- Hardware description languages
- Instruction scheduling

## Related Skills

- `ssa-constructor` - Build SSA form
- `liveness-analysis` - Compute live ranges
- `llvm-backend-generator` - LLVM's register allocators
- `dead-code-eliminator` - Run before allocation

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| Chaitin "Register allocation & spilling via graph coloring" (1982) | Classic graph coloring algorithm |
| Poletto, Sarkar "Linear scan register allocation" (1999) | Fast allocation for JITs |
| Appel "Modern Compiler Implementation" Ch. 11 | Comprehensive treatment |

## Tradeoffs and Limitations

### Approach Tradeoffs

| Approach | Pros | Cons |
|----------|------|------|
| Graph coloring | Optimal allocation | NP-complete, slow |
| Linear scan | O(n) time | Suboptimal allocation |
| Iterated coalescing | Eliminates moves | Complex implementation |

### When NOT to Use This Skill

- When targeting stack machines (no registers)
- For interpreted languages (no native code)
- When using an existing backend (LLVM, Cranelift)

### Limitations

- NP-complete in general
- Spilling can negate benefits
- ABI constraints limit flexibility

## Assessment Criteria

A high-quality implementation should have:

| Criterion | What to Look For |
|-----------|------------------|
| Correctness | No undefined uses, correct spill/reload |
| Efficiency | Minimizes spill code |
| Speed | Fast allocation for JIT use cases |
| Coalescing | Eliminates unnecessary moves |

### Quality Indicators

✅ **Good**: Correct allocation, minimal spills, fast runtime
⚠️ **Warning**: Excessive spilling, slow allocation
❌ **Bad**: Incorrect allocation, uses undefined registers

## Research Tools & Artifacts

Register allocation in compilers:

| Tool | What to Learn |
|------|---------------|
| **LLVM** | Production allocators |
| **Cranelift** | Rust allocator |

## Research Frontiers

### 1. Optimistic Coloring
- **Approach**: Try without spilling first

## Implementation Pitfalls

| Pitfall | Real Consequence | Solution |
|---------|-----------------|----------|
| **Spilling** | Slow code | Minimize spills |
