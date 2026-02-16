---
name: common-subexpression-eliminator
description: 'Implements common subexpression elimination (CSE). Use when: (1) Building
  compilers, (2) Optimizing code, (3) Program analysis.'
version: 1.0.0
tags:
- optimization
- compiler-pass
- cse
- code-motion
difficulty: intermediate
languages:
- python
- rust
dependencies:
- ssa-constructor
---

# Common Subexpression Eliminator

Implements common subexpression elimination optimization.

## When to Use

- Building optimizing compilers
- Program optimization
- Code analysis
- Performance tuning

## What This Skill Does

1. **Identifies redundancy** - Finds repeated computations
2. **Eliminates** - Reuses computed values
3. **Handles memory** - Aliasing considerations
4. **Optimizes** - Global and local CSE

## Key Concepts

| Concept | Description |
|---------|-------------|
| **Available expression** | Computed and not killed |
| **Killing** | Expression invalidated |
| **Global** | Across basic blocks |
| **Conservative** | Avoid aliasing issues |

## Tips

- Handle aliasing conservatively
- Consider side effects
- Use hash for fast comparison
- Track memory operations

## Related Skills

- `constant-propagation-pass` - Constant propagation
- `common-subexpression-eliminator` - DCE
- `ssa-constructor` - Register allocation

## Research Tools & Artifacts

Real-world CSE implementations to study:

| Tool | Why It Matters |
|------|----------------|
| **GCC GIMPLE** | Production CSE in GCC |
| **LLVM SELC** | Scalar evolution-based CSE |
| **MLIR CSE** | dialect-level commoning |
| **GraalVM Truffle** | Partial evaluation with CSE |
| **HotSpot C1/C2** | Client/server compiler CSE |

### Key Optimizations

- **Redundant load elimination (RLE)**: Beyond expression CSE
- **Store CSE**: Common stores to same location
- **Linear-speed redundancy**: Profitable vs redundant

## Research Frontiers

Current CSE research:

| Direction | Key Papers | Challenge |
|-----------|------------|-----------|
| **Value numbering** | "Global Value Numbering" (1999) | More powerful than CSE |
| **SCEV (Scalar Evolution)** | LLVM's SCEV analysis | Loop-carried dependencies |
| **Partial redundancy** | "Partial Redundancy Elimination" (1992) | Redundancy across paths |
| **Bit-level CSE** | "Bitwise CSE" (2011) | Non-overlapping bits |
| **ML-based** | "Learning Optimizations" (2023) | Predicting profitability |

### Hot Topics

1. **Redundancy in quantum circuits**: CSE for quantum compilation
2. **Graph RE**: Redundancy elimination in dataflow graphs
3. **Approximate computing**: Tolerable approximation in CSE

## Implementation Pitfalls

Common CSE bugs:

| Pitfall | Real Example | Prevention |
|---------|--------------|------------|
| **Aliasing violations** | CSE on aliased pointers | Conservative with pointers |
| **Side effects** | CSE removing io operations | Track purity precisely |
| **Memory ordering** | Out-of-order store CSE | Model memory precisely |
| **Division safety** | CSE on division by zero | Check divisor non-zero |
| **Overflow** | CSE changing overflow | Preserve overflow behavior |
| **Load/store ordering** | Reordering loads incorrectly | Model memory model |

### The "Pointer Aliasing" Bug

CSE incorrectly assuming no aliasing:
```c
// May alias - CSE would be wrong
a[i] = x;
b[j] = a[i];  // Could be same as a[i] above!
```

**Solution**: Conservative - don't CSE if pointers could alias.
