---
name: inline-expander
description: "Implement function inlining to eliminate call overhead and enable further optimizations."
version: "1.0.0"
tags: [compilation, optimization, llvm, pldi]
difficulty: intermediate
languages: [c++, rust, python]
dependencies: [ssa-constructor, dead-code-eliminator]
---

# Inline Expander

Function inlining replaces a function call with the body of the called function, eliminating call overhead and enabling further optimizations. It is one of the most important optimizations in compilers.

## When to Use This Skill

- Building optimizing compilers
- Eliminating abstraction overhead
- Enabling interprocedural optimization
- Improving cache locality
- Reducing function call overhead

## What This Skill Does

1. **Call Site Inlining**: Replace call with callee body
2. **Parameter Substitution**: Replace formal parameters with actual arguments
3. **Return Handling**: Replace returns with assignments or gotos
4. **Heuristic Deciding**: Choose which functions to inline
5. **Recursive Inlining**: Handle self-recursive functions

## Key Concepts

| Concept | Description |
|---------|-------------|
| Call Site | Location where a function is called |
| Callee | The function being called |
| Caller | The function making the call |
| Inlining Heuristics | Rules for deciding what to inline |
| Code Bloat | Excessive size growth from inlining |

## Tips

- Inline small, frequently-called functions first
- Be careful with recursive functions (limited unrolling)
- Consider profile-guided optimization for hot call sites
- Run dead code elimination after inlining
- Monitor code size growth

## Common Use Cases

- Eliminating abstraction penalty (getters, small helpers)
- Enabling constant propagation across call boundaries
- Reducing indirect call overhead
- Template instantiation in C++
- Optimizing library functions

## Related Skills

- `dead-code-eliminator` - Clean up after inlining
- `constant-propagation-pass` - Enabled by inlining
- `loop-optimizer` - Combined for maximum effect
- `ssa-constructor` - Simplifies inlining

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| Aycock "A brief history of just-in-time" | Context for inlining importance |
| LLVM Inline Cost Analysis | Production heuristics |
| GCC Inlining Parameters | Tuning guidelines |

## Tradeoffs and Limitations

### Approach Tradeoffs

| Approach | Pros | Cons |
|----------|------|------|
| Always inline | Fast, predictable | Code bloat |
| Size-based | Controls bloat | May miss opportunities |
| Profile-guided | Optimal decisions | Requires profiling |

### When NOT to Use This Skill

- Large functions (causes code bloat)
- Functions called from many places
- Debug builds (need stack traces)
- Recursive functions (infinite growth)

### Limitations

- Can cause significant code size increase
- May hurt instruction cache performance
- Complicates debugging

## Assessment Criteria

A high-quality implementation should have:

| Criterion | What to Look For |
|-----------|------------------|
| Correctness | Preserves program semantics |
| Heuristics | Good tradeoff between speed and size |
| Handling | Deals with returns, recursion |
| Integration | Works with other optimizations |

### Quality Indicators

✅ **Good**: Selective inlining, measurable speedup, controlled size growth
⚠️ **Warning**: Inlines too much or too little
❌ **Bad**: Breaks semantics, causes infinite recursion

## Research Tools & Artifacts

Real-world inlining implementations:

| Tool | Why It Matters |
|------|----------------|
| **LLVM Inliner** | Production inliner with cost model |
| **GCC Inliner** | GCC's inlining passes |
| **JVM JIT** | HotSpot method inlining |
| **V8** | JavaScript inline caching |

### Key Systems

- **LLVM**: State-of-the-art inlining
- **Graal**: Truffle-based inlining

## Research Frontiers

Current inlining research:

| Direction | Key Papers | Challenge |
|-----------|------------|-----------|
| **Cost model** | "Inline Cost Analysis" | Accuracy |
| **PGO** | "Profile-guided Inlining" | Feedback |
| **Specialization** | "Specialization for Inlining" | Dynamic |

### Hot Topics

1. **Machine learning inlining**: Learning inlining decisions
2. **WASM inlining**: WebAssembly optimization

## Implementation Pitfalls

Common inlining bugs:

| Pitfall | Real Example | Prevention |
|---------|--------------|------------|
| **Code bloat** | Too much inlining | Cost model |
| **Compile time** | Inlining slows compile | Limits |
| **Recursive** | Infinite recursion | Cycle detection |
