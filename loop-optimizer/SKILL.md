---
name: loop-optimizer
description: "Optimize loops through transformations like unrolling, fusion, tiling, and vectorization."
version: "1.0.0"
tags: [compilation, optimization, parallelism, pldi]
difficulty: advanced
languages: [c++, rust, python]
dependencies: [dataflow-analysis-framework, ssa-constructor]
---

# Loop Optimizer

Loop optimizations transform loops to improve performance by reducing overhead, increasing parallelism, and improving cache locality. Since programs spend most time in loops, these optimizations are critical for performance.

## When to Use This Skill

- Building optimizing compilers
- Improving numerical code performance
- Enabling vectorization
- Optimizing for cache hierarchy
- Parallelizing loop nests

## What This Skill Does

1. **Loop Unrolling**: Replicate loop body to reduce branch overhead
2. **Loop Fusion**: Combine multiple loops into one
3. **Loop Tiling**: Reorganize iteration for cache locality
4. **Loop Vectorization**: Transform for SIMD execution
5. **Loop Interchange**: Reorder nested loops for memory access

## Key Concepts

| Concept | Description |
|---------|-------------|
| Loop Unrolling | Replicate body to reduce branch overhead |
| Loop Fusion | Combine loops with same bounds |
| Loop Tiling | Reorganize for cache blocks |
| Loop Interchange | Swap nested loop order |
| Vectorization | Execute multiple iterations in parallel |

## Tips

- Profile before optimizing (identify hot loops)
- Consider unrolling factor carefully (code size vs. speed)
- Tile for L1 cache size (typically 32KB)
- Align data for vectorization
- Combine transformations synergistically

## Common Use Cases

- Matrix operations (multiply, transpose)
- Image processing kernels
- Scientific computing
- Machine learning operators
- Compression/decompression

## Related Skills

- `dataflow-analysis-framework` - Dependency analysis
- `constant-propagation-pass` - Combine with loop optimizations
- `llvm-backend-generator` - LLVM loop passes
- `ssa-constructor` - Loop in SSA form

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| Lam, Rothberg, Wolf "The cache performance and optimizations of blocked algorithms" | Classic tiling paper |
| Allen, Kennedy "Optimizing Compilers for Modern Architectures" | Comprehensive loop optimization |
| Polyhedral model papers | Mathematical loop transformation framework |

## Tradeoffs and Limitations

### Approach Tradeoffs

| Approach | Pros | Cons |
|----------|------|------|
| Unrolling | Reduces overhead | Code bloat |
| Tiling | Cache friendly | Complex bounds |
| Vectorization | SIMD speedup | Alignment requirements |

### When NOT to Use This Skill

- Non-critical loops
- When code size matters more than speed
- When loops have complex control flow

### Limitations

- Requires dependency analysis
- May increase code size
- Hardware-specific tuning needed

## Assessment Criteria

A high-quality implementation should have:

| Criterion | What to Look For |
|-----------|------------------|
| Correctness | Preserves loop semantics |
| Performance | Measurable speedup |
| Generality | Handles various loop patterns |
| Safety | Checks for dependencies |

### Quality Indicators

✅ **Good**: Correct transformation, significant speedup, handles dependencies
⚠️ **Warning**: Works for simple cases, fails on complex dependencies
❌ **Bad**: Breaks semantics, incorrect loop bounds

## Research Tools & Artifacts

Real-world loop optimization tools:

| Tool | Why It Matters |
|------|----------------|
| **LLVM loop passes** | Production loop opts |
| **GCC tree-ssa** | GCC loop optimization |
| **Polly (LLVM)** | Polyhedral optimization |
| **ISL** | Integer set library |

### Key Systems

- **Polly**: Polyhedral optimization
- **Halide**: Loop optimization DSL

## Research Frontiers

Current loop optimization research:

| Direction | Key Papers | Challenge |
|-----------|------------|-----------|
| **Polyhedral** | "Polyhedral Model" | Scalability |
| **Auto-tuning** | "Auto-tuning Loops" | Search |
| **SIMD** | "Auto-vectorization" | Vector width |

### Hot Topics

1. **ML for loops**: Learning loop transforms
2. **Quantum loops**: Loop optimization for quantum

## Implementation Pitfalls

Common loop optimization bugs:

| Pitfall | Real Example | Prevention |
|---------|--------------|------------|
| **Dependencies** | Wrong dependence | Analysis |
| **Overflow** | Loop bounds overflow | Careful math |
| **Alignment** | Vector alignment | Pad arrays |
