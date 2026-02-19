---
name: concurrency-verifier
description: "Verify concurrent and parallel programs for data races, deadlocks, and correctness."
version: "1.0.0"
tags: [verification, concurrency, parallelism, oopsla]
difficulty: advanced
languages: [rust, go, java]
dependencies: [hoare-logic-verifier, separation-logician, model-checker]
---

# Concurrency Verifier

Concurrency verification ensures that parallel programs are free from data races, deadlocks, and other concurrency bugs. It is essential for reliable multi-threaded and distributed systems.

## When to Use This Skill

- Verifying multi-threaded programs
- Detecting data races
- Proving deadlock freedom
- Verifying lock protocols
- Building reliable concurrent systems

## What This Skill Does

1. **Race Detection**: Identify unsynchronized shared access
2. **Deadlock Analysis**: Check for potential deadlocks
3. **Lock Verification**: Verify lock usage patterns
4. **Memory Model Reasoning**: Reason about weak memory models
5. **Liveness Checking**: Ensure progress properties

## Key Concepts

| Concept | Description |
|---------|-------------|
| Data Race | Unsynchronized concurrent access to shared data |
| Deadlock | Circular waiting on locks |
| Lock Order | Protocol for acquiring locks to prevent deadlock |
| Ownership | Exclusive access right to data |
| Memory Model | Rules for visibility of writes across threads |

## Tips

- Use consistent lock ordering to prevent deadlocks
- Prefer message passing over shared memory
- Use ownership types when possible (Rust)
- Test with thread sanitizers
- Model check critical sections

## Common Use Cases

- Multi-threaded server verification
- Lock-free data structure verification
- Distributed system verification
- Operating system kernels
- Database concurrency control

## Related Skills

- `separation-logician` - Foundation for concurrent separation logic
- `model-checker` - Exhaustive concurrent state exploration
- `rust-borrow-checker` - Rust's ownership system
- `weak-memory-model-verifier` - For relaxed memory models

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| **O'Hearn, "Resources, Concurrency and Local Reasoning" (TCS 2007)** | Concurrent separation logic |
| **Herlihy & Shavit, "The Art of Multiprocessor Programming"** | Concurrent algorithms |
| **Herlihy & Wing, "Linearizability: A Correctness Condition for Concurrent Objects" (TOPLAS 1990)** | Correctness criterion |

## Tradeoffs and Limitations

### Approach Tradeoffs

| Approach | Pros | Cons |
|----------|------|------|
| Static analysis | Fast | May miss races |
| Model checking | Complete | State explosion |
| Type-based | Compile-time | Conservative |

### When NOT to Use This Skill

- Single-threaded programs
- When testing suffices
- Performance-critical lock-free code (use specialized verification)

### Limitations

- Weak memory models are hard
- Dynamically created threads
- Library callbacks

## Assessment Criteria

A high-quality implementation should have:

| Criterion | What to Look For |
|-----------|------------------|
| Soundness | Catches all races |
| Precision | Few false positives |
| Scalability | Handles realistic programs |
| Usability | Clear error reporting |

### Quality Indicators

✅ **Good**: Catches real races, handles common patterns
⚠️ **Warning**: Many false positives
❌ **Bad**: Misses real races

## Research Tools & Artifacts

Real-world concurrency verification tools:

| Tool | Why It Matters |
|------|----------------|
| **ThreadSanitizer** | Dynamic race detection in LLVM/GCC |
| **CHESS** | Microsoft's deterministic concurrency testing |
| **CalFuzzer** | Dynamic race detection for Java |
| **SPIN** | Model checker for concurrent systems |
| **Verifast** | Concurrent separation logic |
| **Iris** | Higher-order concurrent separation logic |

### Key Verification Systems

- **Rocket** (Amazon): Static verification of DynamoDB
- **SeL4**: Verified microkernel with concurrent reasoning
- **RCC** (Rust): Concurrent verifier for Rust

## Research Frontiers

Current concurrency verification research:

| Direction | Key Papers | Challenge |
|-----------|------------|-----------|
| **Weak memory** | Alglave et al. "Weak Memory Models" | x86/ARM/POWER models |
| **Lock-free** | Various verification approaches | CAS and queues |
| **Linearizability** | Herlihy & Wing (TOPLAS 1990) | Atomic object verification |
| **Fencing** | "Fence Inference" (2015) | Minimal memory fences |
| **Regression** | "Concurrency Bug Detection" (2019) | Finding regression bugs |

### Hot Topics

1. **AI for concurrency**: Learning bug patterns
2. **Quantum concurrency**: Verification of quantum protocols
3. **Distributed systems**: Cross-node verification

## Implementation Pitfalls

Common concurrency verification bugs:

| Pitfall | Real Example | Prevention |
|---------|--------------|------------|
| **Missing volatile** | TSan missed race | Track atomics precisely |
| **Lock ordering violations** | Deadlock not detected | Check lock graph |
| **Signal handlers** | Unsafe signal usage | Model async signals |
| **Atomics vs locks** | Confusion about semantics | Separate verification |
| **Condition variables** | Spurious wakeups | Model precisely |
| **Memory fences** | Weaker than needed | Check fence model |
