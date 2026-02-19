---
name: liveness-analysis
description: "Compute which variables are live at each program point for optimization and register allocation."
version: "1.0.0"
tags: [analysis, optimization, compilers, pldi]
difficulty: intermediate
languages: [c++, rust, python]
dependencies: [dataflow-analysis-framework, control-flow-analysis]
---

# Liveness Analysis

Liveness analysis determines which variables may be used in the future at each program point. It is a fundamental backward dataflow analysis used for register allocation, dead code elimination, and optimization.

## When to Use This Skill

- Register allocation
- Dead code elimination
- Optimizing compiler passes
- Understanding program behavior
- Building IDE features

## What This Skill Does

1. **Live Variable Detection**: Find variables that may be used later
2. **Backward Dataflow**: Propagate information from uses to definitions
3. **Control Flow Handling**: Merge information at join points
4. **Register Allocation**: Map live ranges to registers
5. **Dead Code Detection**: Find dead stores

## Key Concepts

| Concept | Description |
|---------|-------------|
| Live Variable | Variable that may be used before being redefined |
| Live Range | Instructions where a variable is live |
| Use | Instruction that reads a variable |
| Definition | Instruction that writes a variable |
| Backward Analysis | Information flows from uses to definitions |

## Tips

- Run in reverse order for efficiency
- Use worklist algorithm for large functions
- Consider SSA form for simpler analysis
- Combine with register allocation
- Use for dead code detection

## Common Use Cases

- Register allocation
- Dead code elimination
- Live variable debugging
- Memory optimization
- SSA construction

## Related Skills

- `dataflow-analysis-framework` - General framework
- `register-allocator` - Uses liveness info
- `dead-code-eliminator` - Uses liveness to find dead code
- `ssa-constructor` - Uses liveness for phi placement

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| **Aho et al., "Compilers: Principles, Techniques, and Tools", Ch. 9 (1986)** | Classic treatment |
| **Muchnick, "Advanced Compiler Design and Implementation", Ch. 9 (1997)** | Detailed algorithms |
| **Cytron et al., "Efficiently Computing Static Single Assignment Form" (TOPLAS 1991)** | SSA liveness |

## Tradeoffs and Limitations

### Approach Tradeoffs

| Approach | Pros | Cons |
|----------|------|------|
| Simple backward | Easy to implement | O(n²) worst case |
| Worklist | Efficient | More complex |
| SSA-based | Simpler liveness | Requires SSA |

### When NOT to Use This Skill

- Simple stack machines (no register allocation)
- Interpreted languages with unlimited locals
- When memory is not constrained

### Limitations

- Conservative (may overestimate liveness)
- Does not consider aliasing
- Path-sensitive liveness is expensive

## Assessment Criteria

A high-quality implementation should have:

| Criterion | What to Look For |
|-----------|------------------|
| Correctness | Sound over-approximation |
| Efficiency | Reasonable runtime |
| Handling | Deals with loops, branches |
| Integration | Works with CFG |

### Quality Indicators

✅ **Good**: Correct liveness, efficient algorithm, handles all control flow
⚠️ **Warning**: Slow on large functions, doesn't handle loops
❌ **Bad**: Incorrect results, misses live variables

## Research Tools & Artifacts

Real-world liveness analysis tools:

| Tool | Why It Matters |
|------|----------------|
| **LLVM** | Production liveness in LLVM |
| **GCC** | GCC dataflow framework |
| **Soot** | Java bytecode analysis |
| **MIRAI** | Rust liveness analysis |

### Key Systems

- **LLVM**: SSA-based liveness
- **Graal**: Truffle liveness

## Research Frontiers

Current liveness analysis research:

| Direction | Key Papers | Challenge |
|-----------|------------|-----------|
| **Precise liveness** | "Precise Liveness" | Aliasing |
| **Incremental** | "Incremental Liveness" | Change impact |
| **Parallel** | "Parallel Liveness" | Multi-core |

### Hot Topics

1. **WASM liveness**: Binary liveness
2. **ML liveness**: Learning liveness

## Implementation Pitfalls

Common liveness bugs:

| Pitfall | Real Example | Prevention |
|---------|--------------|------------|
| **Aliasing** | Pointer aliasing | Conservative |
| **Memory** | Large programs | Incremental |
