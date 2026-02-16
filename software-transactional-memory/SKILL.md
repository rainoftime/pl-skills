---
name: software-transactional-memory
description: 'Implements software transactional memory. Use when: (1) Building concurrent
  data structures, (2) Simplifying lock-free code, (3) Composing atomic operations.'
version: 1.0.0
tags:
- concurrency
- stm
- transactions
- synchronization
difficulty: intermediate
languages:
- haskell
- rust
dependencies: []
---

# Software Transactional Memory

Implements STM for lock-free concurrent programming.

## When to Use

- Concurrent data structure design
- Simplifying lock-free algorithms
- Composing atomic operations
- Database-style transactions in memory

## What This Skill Does

1. **Implements transactions** - Atomic read/write blocks
2. **Handles conflicts** - Conflict detection and retry
3. **Provides composability** - Transactional composition
4. **Optimizes performance** - Read/write sets

## Key Concepts

| Concept | Description |
|---------|-------------|
| **Read set** | Variables read in transaction |
| **Write set** | Variables written in transaction |
| **Commit** | Validate and apply writes |
| **Abort** | Discard changes, restart |
| **Retry** | Wait for condition, restart |
| **OrElse** | Alternative on abort |

## STM Properties

- **Atomicity**: All or nothing
- **Isolation**: No intermediate states visible
- **Consistency**: Maintain invariants
- **Composability**: Combine operations

## Tips

- Keep transactions short
- Avoid long-running operations
- Use retry for blocking
- Consider contention patterns
- Profile abort rates

## Related Skills

- `actor-model-implementer` - Actor concurrency
- `race-detection-tool` - Race detection
- `weak-memory-model-verifier` - Verify concurrency

## Research Tools & Artifacts

STM implementations:

| System | Language | What to Learn |
|--------|----------|---------------|
| **Haskell STM** | Haskell | Original STM |
| **Clojure refs** | Clojure | Production STM |
| **Intel STM** | C/C++ | Hardware support |
| **TinySTM** | C | Fast STM |

### Key Papers

- **Herlihy & Moss** - STM paper
- **Harris et al.** - Composable memory transactions

## Research Frontiers

### 1. Hardware Transactional Memory
- **Goal**: Hardware support for transactions
- **Approach**: TSX, HTM
- **Tools**: Intel TSX

## Implementation Pitfalls

| Pitfall | Real Consequence | Solution |
|---------|-----------------|----------|
| **Starvation** | Transactions never commit | Bounded retries |
| **Contention** | High abort rate | Careful design |
