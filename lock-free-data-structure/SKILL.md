---
name: lock-free-data-structure
description: "Implement lock-free and wait-free data structures for high-concurrency systems."
version: "1.0.0"
tags: [concurrency, lock-free, data-structures, oopsla]
difficulty: advanced
languages: [rust, c++, java]
dependencies: [concurrency-verifier, memory-allocator]
---

# Lock-Free Data Structure

Lock-free data structures allow multiple threads to access shared data without using locks, enabling better scalability and avoiding issues like deadlocks and priority inversion.

## When to Use This Skill

- Building high-performance concurrent systems
- Avoiding lock-related issues (deadlocks, convoying)
- Real-time systems requiring wait-free guarantees
- High-contention scenarios
- Scalable server applications

## What This Skill Does

1. **CAS Operations**: Use compare-and-swap for atomic updates
2. **Memory Reclamation**: Safe memory reclamation (hazard pointers, RCU)
3. **ABA Prevention**: Handle ABA problem in lock-free algorithms
4. **Progress Guarantees**: Ensure lock-free or wait-free progress
5. **Correctness Verification**: Prove linearizability

## Key Concepts

| Concept | Description |
|---------|-------------|
| CAS | Compare-And-Swap atomic operation |
| Lock-Free | At least one thread makes progress |
| Wait-Free | Every thread completes in bounded steps |
| Linearizability | Operations appear atomic |
| ABA Problem | Value changes A→B→A, CAS succeeds incorrectly |
| Hazard Pointer | Safe memory reclamation scheme |

## Tips

- Use atomic primitives (CAS, FAA) for lock-free code
- Implement safe memory reclamation (hazard pointers, EBR)
- Be aware of the ABA problem
- Test extensively with thread sanitizers
- Consider using existing libraries (crossbeam, kotlinx)

## Common Use Cases

- High-throughput message queues
- Concurrent caches
- Real-time trading systems
- Game engines
- Database systems

## Related Skills

- `concurrency-verifier` - Verify correctness
- `message-passing-system` - Alternative concurrency model
- `memory-allocator` - Lock-free allocators
- `transactional-memory` - Alternative to lock-free

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| Herlihy, Shavit "The Art of Multiprocessor Programming" | Comprehensive treatment |
| Michael, Scott "Simple, Fast, and Practical Non-Blocking Queue" | Classic queue algorithm |
| Michael "Hazard Pointers" | Memory reclamation |

## Tradeoffs and Limitations

### Approach Tradeoffs

| Approach | Pros | Cons |
|----------|------|------|
| Lock-free | No deadlocks, scalable | Complex, ABA issues |
| Wait-free | Guaranteed progress | Very complex |
| Lock-based | Simple | Deadlocks, contention |

### When NOT to Use This Skill

- Low-contention scenarios (locks are fine)
- When simplicity is more important than performance
- When memory ordering is platform-specific

### Limitations

- Memory reclamation is tricky
- ABA problem requires careful handling
- Not all algorithms have lock-free versions

## Assessment Criteria

A high-quality implementation should have:

| Criterion | What to Look For |
|-----------|------------------|
| Correctness | Linearizable operations |
| Progress | Lock-free or wait-free |
| Safety | No use-after-free |
| Performance | Scales with thread count |

### Quality Indicators

✅ **Good**: Linearizable, proper memory reclamation, handles ABA
⚠️ **Warning**: Works but has memory safety issues
❌ **Bad**: Race conditions, memory leaks, not actually lock-free

## Research Tools & Artifacts

Real-world lock-free data structures:

| Tool | Why It Matters |
|------|----------------|
| **crossbeam (Rust)** | Lock-free data structures |
| **ConcurrentSkipList** | Java concurrent skiplist |
| **ConcurrentHashMap** | Java CHM |
| **boost.lockfree** | C++ lock-free |
| **disruptor** | LMAX Disruptor |

### Key Libraries

- **crossbeam**: Rust concurrency
- **java.util.concurrent**: Java concurrent

## Research Frontiers

Current lock-free research:

| Direction | Key Papers | Challenge |
|-----------|------------|-----------|
| **Linearizability** | "Linearizability" (1990) | Verification |
| **Epoch-based** | "Epoch Reclamation" | Memory reclamation |
| **Hybrid** | "Hybrid Reclamation" | Combining approaches |

### Hot Topics

1. **Lock-free for Wasm**: WebAssembly concurrency
2. **Quantum lock-free**: Quantum data structures

## Implementation Pitfalls

Common lock-free bugs:

| Pitfall | Real Example | Prevention |
|---------|--------------|------------|
| **ABA** | CAS succeeds on reused node | Tag pointers |
| **Memory** | Use-after-free | Hazard pointers |
| **Ordering** | Wrong memory order | Careful ordering |
