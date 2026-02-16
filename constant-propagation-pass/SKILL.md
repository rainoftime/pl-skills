---
name: constant-propagation-pass
description: 'Implements constant propagation optimization. Use when: (1) Building
  compilers, (2) Learning program analysis, (3) Implementing optimizations.'
version: 1.0.0
tags:
- optimization
- compiler-pass
- dataflow
- constant-folding
difficulty: beginner
languages:
- python
- rust
dependencies:
- dataflow-analysis-framework
---

# Constant Propagation Pass

Implements dataflow constant propagation optimization.

## When to Use

- Building compilers
- Learning program analysis
- Implementing optimizations
- Static program analysis

## What This Skill Does

1. **Collects constants** - Tracks known values
2. **Propagates** - Forward dataflow analysis
3. **Optimizes** - Replaces with constants
4. **Handles conservativeness** - UNK for unknown

## Key Concepts

| Concept | Description |
|---------|-------------|
| **Lattice** | Partial order for analysis |
| **Transfer** | How statements transform lattice |
| **Meet** | Lattice meet (greatest lower bound) |
| **Join** | Lattice join (least upper bound) |
| **Worklist** | Iterative algorithm |

## Tips

- Use join at control flow merge points
- Handle conservatively (NAC for unknown)
- Consider arrays and pointers
- Combine with copy propagation

## Related Skills

- `common-subexpression-eliminator` - CSE optimization
- `common-subexpression-eliminator` - DCE optimization
- `dataflow-analysis-framework` - General dataflow

## Research Tools & Artifacts

Compiler optimization tools:

| Tool | What to Learn |
|------|---------------|
| **LLVM** | Industrial optimization |
| **GCC GIMPLE** | GCC optimization |

## Research Frontiers

### 1. SSA-Based Optimization
- **Goal**: Optimize using SSA form

## Implementation Pitfalls

| Pitfall | Real Consequence | Solution |
|---------|-----------------|----------|
| **Wrong meet** | Imprecision | Use correct lattice |
