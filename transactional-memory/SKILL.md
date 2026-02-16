---
name: transactional-memory
description: "Implement software transactional memory (STM) for composable concurrent programming."
version: "1.0.0"
tags: [concurrency, transactions, stm, oopsla]
difficulty: advanced
languages: [haskell, rust, python]
dependencies: [concurrency-verifier, lock-free-data-structure]
---

# Transactional Memory

Software Transactional Memory (STM) provides a composable abstraction for concurrent programming. Transactions appear atomic - they either complete entirely or have no effect.

## When to Use This Skill

- Composable concurrent abstractions
- Avoiding lock composition problems
- Building concurrent data structures
- High-level concurrent programming
- Teaching concurrency concepts

## What This Skill Does

1. **Atomic Blocks**: Execute code atomically
2. **Transactional Variables**: Shared mutable state
3. **Retry/OrElse**: Blocking and alternative transactions
4. **Conflict Detection**: Detect conflicting transactions
5. **Rollback**: Abort and retry on conflicts

## Key Concepts

| Concept | Description |
|---------|-------------|
| TVar | Transactional variable |
| Transaction | Sequence of operations |
| Atomic | All-or-nothing execution |
| Retry | Block until change |
| OrElse | Alternative transactions |
| Optimistic | Assume no conflicts, retry if wrong |

## Tips

- Keep transactions short for better performance
- Use retry for blocking semantics
- Use orElse for alternatives
- Avoid I/O inside transactions
- Consider read/write patterns

## Common Use Cases

- Concurrent data structures
- Composable synchronization
- Gaming state management
- Database-like transactions in memory
- Teaching concurrency

## Related Skills

- `lock-free-data-structure` - Alternative approach
- `concurrency-verifier` - Verify correctness
- `effect-system` - Track transaction effects
- `hoare-logic-verifier` - Prove correctness

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| Shavit, Touitou "Software Transactional Memory" | Original STM paper |
| Harris et al. "Composable Memory Transactions" | Haskell STM |
| Herlihy, Moss "Transactional Memory" | Hardware TM |

## Tradeoffs and Limitations

### Approach Tradeoffs

| Approach | Pros | Cons |
|----------|------|------|
| Optimistic STM | No blocking | Retries under contention |
| Pessimistic STM | Fewer retries | More blocking |
| Hardware TM | Fast | Limited capacity |

### When NOT to Use This Skill

- Low-contention scenarios
- Performance-critical code
- When simple locks suffice

### Limitations

- I/O cannot be rolled back
- High contention causes retries
- Memory overhead

## Assessment Criteria

A high-quality implementation should have:

| Criterion | What to Look For |
|-----------|------------------|
| Atomicity | All-or-nothing |
| Isolation | No partial visibility |
| Composability | Transactions combine |
| Performance | Reasonable overhead |

### Quality Indicators

✅ **Good**: Composable, retry works, good performance
⚠️ **Warning**: High retry rate under contention
❌ **Bad**: Not atomic, memory leaks

## Research Tools & Artifacts

Real-world STM implementations:

| Tool | Why It Matters |
|------|----------------|
| **Haskell STM** | Production STM |
| **Clojure refs** | STM in Clojure |
| **Intel TM** | Hardware TM |
| **Rust STM** | STM for Rust |

### Key Systems

- **Haskell STM**: Research STM
- **STM.NET**: .NET STM

## Research Frontiers

Current STM research:

| Direction | Key Papers | Challenge |
|-----------|------------|-----------|
| **Performance** | "Scalable STM" | Contention |
| **Persistence** | "Persistent STM" | Durability |

### Hot Topics

1. **Wasm STM**: WebAssembly transactions
2. **Hybrid TM**: Hardware + software

## Implementation Pitfalls

Common STM bugs:

| Pitfall | Real Example | Prevention |
|---------|--------------|------------|
| **I/O in tx** | I/O not rolled back | Don't do I/O |
| **Starvation** | Live lock | Backoff |
