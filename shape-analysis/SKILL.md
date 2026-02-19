---
name: shape-analysis
description: "Analyze the shape of heap data structures to enable precise reasoning about pointer-rich data."
version: "1.0.0"
tags: [analysis, pointers, verification, oopsla]
difficulty: advanced
languages: [c, java, python]
dependencies: [alias-and-points-to-analysis, separation-logician]
---

# Shape Analysis

Shape analysis determines the "shape" of heap data structures (lists, trees, cycles) at each program point. It enables precise reasoning about programs that manipulate pointer-based data structures.

## When to Use This Skill

- Verifying pointer-manipulating programs
- Detecting memory leaks and corruption
- Optimizing heap traversal
- Analyzing linked data structures
- Building verification tools

## What This Skill Does

1. **Shape Inference**: Determine data structure shapes (list, tree, cycle)
2. **Heap Abstraction**: Model heap configurations abstractly
3. **Pointer Aliasing**: Track aliasing relationships
4. **Structure Recognition**: Identify patterns (linked list, tree)
5. **Invariant Discovery**: Find shape invariants

## Key Concepts

| Concept | Description |
|---------|-------------|
| Shape Graph | Abstract representation of heap structure |
| Shape | Classification (list, tree, cycle, etc.) |
| Heap Abstraction | Summarize multiple concrete heaps |
| Canonicalization | Normalize shape representations |
| Materialization | Create concrete nodes from summary |

## Tips

- Use shape graphs for moderate precision
- TVLA provides better precision at higher cost
- Separation logic enables compositional reasoning
- Focus on relevant predicates for scalability
- Use widening for loops

## Common Use Cases

- Memory safety verification
- Data structure invariant checking
- Memory leak detection
- Program understanding
- Optimization of pointer-intensive code

## Related Skills

- `alias-and-points-to-analysis` - Points-to and alias analysis
- `separation-logician` - Separation logic for shapes
- `alias-and-points-to-analysis` - Alias relationships
- `hoare-logic-verifier` - Verification with shapes

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| **Sagiv, Reps, Wilhelm, "Parametric Shape Analysis via 3-Valued Logic" (POPL 1999/TOPLAS 2002)** | TVLA framework |
| **Distefano, O'Hearn, Yang, "A Local Shape Analysis Based on Separation Logic" (TACAS 2006)** | Separation logic shapes |
| **Jones & Muchnick, "A Flexible Approach to Pointer Analysis" (POPL 1982)** | Shape graphs |

## Tradeoffs and Limitations

### Approach Tradeoffs

| Approach | Pros | Cons |
|----------|------|------|
| Shape graphs | Simple, intuitive | Limited precision |
| TVLA | Precise | Expensive |
| Separation logic | Compositional | Requires annotations |

### When NOT to Use This Skill

- Programs without dynamic allocation
- When points-to analysis suffices
- Performance-critical compilation time

### Limitations

- Precision vs. cost trade-off
- Complex data structures hard to handle
- May need programmer annotations

## Assessment Criteria

A high-quality implementation should have:

| Criterion | What to Look For |
|-----------|------------------|
| Soundness | Never miss a possible shape |
| Precision | Distinguish common patterns |
| Efficiency | Reasonable analysis time |
| Usability | Clear output format |

### Quality Indicators

✅ **Good**: Recognizes lists, trees, cycles; handles loops
⚠️ **Warning**: Only basic shapes, loses precision in loops
❌ **Bad**: Returns UNKNOWN for all structures

## Research Tools & Artifacts

Real-world shape analysis tools:

| Tool | Why It Matters |
|------|----------------|
| **TVLA** | Shape analysis framework |
| **Infer** | Facebook shape analysis |
| **Separator** | Separation logic analysis |
| **Space** | Galois shape analysis |

### Key Systems

- **Facebook Infer**: Industrial shape analysis
- **SepAnalyst**: Verification tool

## Research Frontiers

Current shape analysis research:

| Direction | Key Papers | Challenge |
|-----------|------------|-----------|
| **Automation** | "Automatic Shape" | Scale |
| **Parallel** | "Parallel Shape" | Multi-core |

### Hot Topics

1. **Shape for Rust**: Ownership shapes
2. **Shape for Wasm**: Binary shapes

## Implementation Pitfalls

Common shape analysis bugs:

| Pitfall | Real Example | Prevention |
|---------|--------------|------------|
| **Precision** | Too coarse | Refine |
| **Performance** | Slow | Widen |
