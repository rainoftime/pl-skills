---
name: escape-analysis
description: "Determine if objects escape their defining scope to enable stack allocation and optimization."
version: "1.0.0"
tags: [analysis, optimization, memory, oopsla]
difficulty: advanced
languages: [java, rust, python]
dependencies: [alias-and-points-to-analysis, interprocedural-analysis]
---

# Escape Analysis

Escape analysis determines whether objects allocated in a method can be accessed outside that method. This enables optimizations like stack allocation, lock elision, and scalar replacement.

## When to Use This Skill

- Optimizing memory allocation
- Eliminating unnecessary synchronization
- Enabling scalar replacement
- Building JIT compilers
- Reducing GC pressure

## What This Skill Does

1. **Escape Detection**: Identify objects that escape their scope
2. **Interprocedural Analysis**: Track escapes through method calls
3. **Stack Allocation**: Allocate non-escaping objects on stack
4. **Lock Elision**: Remove unnecessary synchronization
5. **Scalar Replacement**: Replace objects with scalar variables

## Key Concepts

| Concept | Description |
|---------|-------------|
| Escape | Object accessible outside its creating method |
| No Escape | Object stays local, can be stack-allocated |
| Arg Escape | Object escapes via method parameter |
| Global Escape | Object escapes via return or static field |
| Scalar Replacement | Replace object with individual fields |

## Tips

- Run after inlining for best results
- Combine with points-to analysis for precision
- Use for lock elision in synchronized code
- Profile to identify optimization opportunities
- Consider object size for stack allocation

## Common Use Cases

- Stack allocation optimization
- Lock elision (remove unnecessary synchronized)
- Scalar replacement of aggregates
- Reducing GC pressure
- JVM JIT optimization

## Related Skills

- `alias-and-points-to-analysis` - Foundation for points-to and alias analysis
- `interprocedural-analysis` - Method-level analysis
- `garbage-collector-implementer` - Uses escape info
- `inline-expander` - Exposes more escape opportunities

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| Choi, Gupta, Serrano "Escape analysis for Java" (1999) | OOPSLA paper on Java escape analysis |
| Blanchet "Escape analysis for Java" (2003) | Algorithm improvements |
| Kotzmann et al. "Design of the Java HotSpot Client Compiler" | Production implementation |

## Tradeoffs and Limitations

### Approach Tradeoffs

| Approach | Pros | Cons |
|----------|------|------|
| Intraprocedural | Fast | Misses interprocedural escapes |
| Interprocedural | More precise | Expensive |
| Flow-sensitive | Most precise | Very expensive |

### When NOT to Use This Skill

- Programs with minimal object allocation
- When allocation cost is negligible
- For single-use scripts

### Limitations

- Requires whole-program analysis for full precision
- Reflection can cause unexpected escapes
- Native code can cause unknown escapes

## Assessment Criteria

A high-quality implementation should have:

| Criterion | What to Look For |
|-----------|------------------|
| Soundness | Never miss an escape |
| Precision | Minimize false positives |
| Efficiency | Reasonable compile time |
| Optimization | Enable real speedups |

### Quality Indicators

✅ **Good**: Catches all escapes, enables significant optimization
⚠️ **Warning**: Conservative (many false positives)
❌ **Bad**: Misses escapes, causes runtime errors

## Research Tools & Artifacts

Real-world escape analysis implementations:

| Tool | Why It Matters |
|------|----------------|
| **Java HotSpot** | Production escape analysis in JVM |
| **J9 JVM** | IBM's JVM escape analysis |
| **GraalVM** | Truffle-based escape analysis |
| **V8** | JavaScript escape analysis |
| **CLR** | .NET escape analysis |

### Key Papers

- **Choi et al.**: Original escape analysis paper
- **Blanchet**: Escape analysis improvements

## Research Frontiers

Current escape analysis research:

| Direction | Key Papers | Challenge |
|-----------|------------|-----------|
| **Concurrency** | "Escape Analysis for Concurrency" | Thread escape |
| **Partial escape** | "Partial Escape Analysis" | Some fields escape |
| **Escape in ML** | "Escape Analysis for ML" | Functional escape |

### Hot Topics

1. **Escape for parallelism**: Enabling parallelism
2. **Escape for memory**: Stack allocation decisions

## Implementation Pitfalls

Common escape analysis bugs:

| Pitfall | Real Example | Prevention |
|---------|--------------|------------|
| **Reflection** | Class.forName escapes | Model reflection |
| **Native** | JNI causes escapes | Conservative |
| **Threads** | Thread.start escapes | Thread analysis |
