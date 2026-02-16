---
name: dead-code-eliminator
description: "Eliminate unreachable and unused code to reduce program size and improve performance."
version: "1.0.0"
tags: [compilation, optimization, llvm, pldi]
difficulty: intermediate
languages: [c++, rust, python]
dependencies: [dataflow-analysis-framework, control-flow-analysis]
---

# Dead Code Eliminator

Dead code elimination (DCE) removes code that has no effect on program output, including unreachable code, unused computations, and redundant assignments. It is a fundamental optimization in compilers.

## When to Use This Skill

- Optimizing compiler passes
- Reducing binary size
- Improving cache utilization
- Cleaning up generated code
- Minifying code for distribution

## What This Skill Does

1. **Unreachable Code Elimination**: Remove code that cannot be executed
2. **Dead Variable Elimination**: Remove computations of unused values
3. **Dead Store Elimination**: Remove writes that are never read
4. **Dead Function Elimination**: Remove functions that are never called
5. **Aggressive DCE**: Iteratively remove dead code until fixpoint

## Key Concepts

| Concept | Description |
|---------|-------------|
| Dead Code | Code that has no effect on program output |
| Unreachable Code | Code that cannot be executed |
| Live Variable | Variable that may be used later |
| Critical Instruction | Instruction with side effects |
| Fixpoint | State where no more changes occur |

## Tips

- Run DCE after inlining to clean up unused parameters
- Combine with constant propagation for better results
- Use SSA form for simpler liveness analysis
- Run iteratively until fixpoint
- Be careful with memory-mapped I/O (appears dead)

## Common Use Cases

- Post-inlining cleanup
- Tree shaking in JavaScript bundlers
- Removing debug code in production
- Optimizing generated code
- Binary size reduction

## Related Skills

- `constant-propagation-pass` - Often combined with DCE
- `inline-expander` - Creates dead code opportunities
- `dataflow-analysis-framework` - Foundation for liveness
- `ssa-constructor` - Simplifies analysis

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| Muchnick "Advanced Compiler Design" Ch. 18 | Comprehensive treatment |
| Click "Global code motion/global value numbering" | Modern DCE approach |
| LLVM Dead Code Elimination Pass | Production implementation |

## Tradeoffs and Limitations

### Approach Tradeoffs

| Approach | Pros | Cons |
|----------|------|------|
| Simple DCE | Fast, easy | Misses opportunities |
| Aggressive DCE | Removes more code | More complex |
| ADCE with interprocedural | Global optimization | Very expensive |

### When NOT to Use This Skill

- When code size is not a concern
- For debug builds (keep code for debugging)
- When side effects are unclear (volatile, I/O)

### Limitations

- May remove intentionally dead code (defensive programming)
- Cannot remove code that might have side effects
- Interprocedural DCE requires whole-program analysis

## Assessment Criteria

A high-quality implementation should have:

| Criterion | What to Look For |
|-----------|------------------|
| Soundness | Never removes code that affects output |
| Completeness | Removes all provably dead code |
| Speed | Fast enough for production use |
| Iteration | Reaches fixpoint |

### Quality Indicators

✅ **Good**: Removes all dead code, preserves semantics, fast
⚠️ **Warning**: Removes some but not all dead code
❌ **Bad**: Removes code that affects program output

## Research Tools & Artifacts

Real-world DCE implementations:

| Tool | Why It Matters |
|------|----------------|
| **LLVM DCE pass** | Production DCE in LLVM |
| **GCC DCE** | GCC's dead code elimination |
| **Soot DCE** | Java bytecode DCE |
| **GraalVM DCE** | Truffle-based DCE |

### Key Optimizations

- **ADCE (Aggressive DCE)**: More aggressive than standard
- **LICM with DCE**: Loop-invariant code motion

## Research Frontiers

Current DCE research:

| Direction | Key Papers | Challenge |
|-----------|------------|-----------|
| **Interprocedural DCE** | "Whole-program DCE" | Cross-module analysis |
| **Type-based DCE** | "Type-driven DCE" | Type information |
| **Dynamically dead** | "Dynamic Dead Code" | Runtime dead code |

### Hot Topics

1. **DCE for microservices**: Removing unused endpoints
2. **Web bundle optimization**: Tree-shaking in bundlers

## Implementation Pitfalls

Common DCE bugs:

| Pitfall | Real Example | Prevention |
|---------|--------------|------------|
| **Side effects** | Removing print statements | Track I/O precisely |
| **Volatile** | Removing volatile reads | Handle volatile |
| **Finalizers** | Removing finalize() | Don't remove finalizers |
| **Self-modifying** | Removing JIT code | Handle dynamic code |
