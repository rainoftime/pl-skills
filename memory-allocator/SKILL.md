---
name: memory-allocator
description: "Implement memory allocators for efficient dynamic memory management in language runtimes."
version: "1.0.0"
tags: [runtime, memory, systems, pldi]
difficulty: advanced
languages: [c, rust, c++]
dependencies: [garbage-collector-implementer]
---

# Memory Allocator

Memory allocators manage dynamic memory allocation and deallocation, a critical component of language runtimes. Different allocation strategies optimize for different workloads.

## When to Use This Skill

- Implementing language runtimes
- Building custom allocators
- Optimizing memory performance
- Embedded systems development
- Understanding memory management

## What This Skill Does

1. **Block Allocation**: Allocate fixed-size blocks efficiently
2. **Heap Management**: Organize free memory
3. **Allocation Strategies**: First-fit, best-fit, segregated fit
4. **Fragmentation Control**: Minimize internal/external fragmentation
5. **Deallocation**: Free memory and coalesce blocks

## Key Concepts

| Concept | Description |
|---------|-------------|
| Block | Contiguous memory region |
| Fragmentation | Wasted space (internal or external) |
| Free List | Linked list of free blocks |
| Coalescing | Merge adjacent free blocks |
| Slab | Pre-allocated block for fixed-size objects |

## Tips

- Use slab allocators for fixed-size objects
- Use arena allocators for temporary allocations
- Consider alignment requirements
- Profile before optimizing allocation
- Use generation counters for safe references

## Common Use Cases

- Language runtime allocators
- Game engines (arena allocators)
- Database buffer pools
- Embedded systems
- High-performance systems

## Related Skills

- `garbage-collector-implementer` - Automatic memory management
- `escape-analysis` - Optimize allocation
- `jit-compiler-builder` - JIT allocation

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| Wilson et al. "Dynamic Storage Allocation" | Survey of algorithms |
| Bonwick "The Slab Allocator" | Linux slab allocator |
| Berger et al. "Hoard" | Scalable multicore allocator |

## Tradeoffs and Limitations

### Approach Tradeoffs

| Approach | Pros | Cons |
|----------|------|------|
| Bump pointer | Very fast | Cannot free individually |
| Free list | Can free | Fragmentation |
| Slab | No fragmentation | Fixed size only |

### When NOT to Use This Skill

- When OS allocator suffices
- For small programs
- When memory is not a concern

### Limitations

- Thread safety requires synchronization
- Fragmentation is hard to eliminate
- Cannot allocate more than capacity

## Assessment Criteria

A high-quality implementation should have:

| Criterion | What to Look For |
|-----------|------------------|
| Correctness | No corruption, double-free safe |
| Efficiency | Low allocation overhead |
| Fragmentation | Reasonable memory usage |
| Safety | Bounds checking |

### Quality Indicators

✅ **Good**: Correct, efficient, handles edge cases
⚠️ **Warning**: Fragmentation issues
❌ **Bad**: Memory corruption, crashes

## Research Tools & Artifacts

Real-world memory allocators:

| Tool | Why It Matters |
|------|----------------|
| **jemalloc** | Facebook allocator |
| **tcmalloc** | Google allocator |
| **Hoard** | Scalable allocator |
| **snmalloc** | Microsoft's allocator |
| **RPMalloc** | Fast allocator |

### Key Systems

- **jemalloc**: Production allocator
- **tcmalloc**: glibc allocator

## Research Frontiers

Current allocator research:

| Direction | Key Papers | Challenge |
|-----------|------------|-----------|
| **Scalable** | "Scalable Allocators" | Multi-core |
| **NUMA** | "NUMA-aware" | Memory hierarchy |
| **Large** | "Large allocators" | Big data |

### Hot Topics

1. **Allocator for Wasm**: WebAssembly allocation
2. **Allocator for Rust**: Custom allocators

## Implementation Pitfalls

Common allocator bugs:

| Pitfall | Real Example | Prevention |
|---------|--------------|------------|
| **Fragmentation** | Memory fragmentation | Slab alloc |
| **Thread contention** | Lock contention | Per-thread pools |
| **Memory** | Memory corruption | Bounds checking |
