---
name: garbage-collector-implementer
description: 'Implements tracing garbage collectors. Use when: (1) Building language
  runtimes, (2) Learning memory management, (3) Optimizing memory allocation.'
version: 1.0.0
tags:
- runtime
- garbage-collection
- memory-management
- systems
difficulty: intermediate
languages:
- c
- rust
- c++
dependencies: []
---

# Garbage Collector Implementer

Implements tracing garbage collectors (mark-compact, generational, etc.).

## When to Use

- Building language runtimes
- Implementing interpreters/compilers
- Learning memory management
- Optimizing memory allocation

## What This Skill Does

1. **Implements heap allocation** - Object layout and allocation
2. **Builds tracing collectors** - Mark-sweep, mark-compact, copying
3. **Handles roots** - Stack and global roots
4. **Optimizes** - Generational, incremental collection

## Key Concepts

| Concept | Description |
|---------|-------------|
| **Root set** | Initial reachable references (stack, globals) |
| **Tracing** | Follow pointers from roots to find live objects |
| **Allocation** | Finding space for new objects |
| **Compaction** | Defragment heap after collection |
| **Generations** | Age-based collection (young/old) |

## GC Algorithms Comparison

| Algorithm | Pros | Cons |
|-----------|------|------|
| **Mark-Sweep** | Simple, no copying | Fragmentation, pause |
| **Mark-Compact** | No fragmentation | Multiple passes, slow |
| **Copying** | Fast, no fragmentation | Half memory, mutator copies |
| **Generational** | Short pause, efficiency | Complexity |

## Tips

- Track all root pointers carefully
- Handle weak references specially
- Consider write barriers for incremental collection
- Profile pause times in production
- Use thread-local allocation for speed

## Related Skills

- `jit-compiler-builder` - Build VM runtime
- `lambda-calculus-interpreter` - Bytecode interpreter

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| **Jones & Lins, "Garbage Collection: Algorithms for Automatic Dynamic Memory Management" (Wiley, 1996)** | Definitive textbook on GC |
| **Jones, Hosking & Moss, "The Garbage Collection Handbook: The Art of Automatic Memory Management" (Chapman & Hall, 2012)** | Updated comprehensive reference |
| **Lieberman & Hewitt, "A Real-Time Garbage Collector Based on the Lifetimes of Objects" (CACM 1983)** | Generational GC origin |
| **Ungar, "Generation Scavenging: A Non-disruptive High Performance Storage Reclamation Algorithm" (1984)** | Nursery/tenured generations |
| **Blackburn & McKinley, "Immix: A Mark-Region Garbage Collector with Space Efficiency, Fast Collection, and Mutator Performance" (PLDI 2008)** | Modern high-throughput collector |

## Tradeoffs and Limitations

### Algorithm Tradeoffs

| Algorithm | Pause Time | Throughput | Memory | Best For |
|-----------|------------|------------|--------|----------|
| **Mark-Sweep** | Medium | Medium | High | Embedded systems |
| **Mark-Compact** | High | Low | High | Long-running servers |
| **Copying** | Low | High | 50% | Real-time, short-lived objects |
| **Generational** | Low | High | Moderate | General purpose |
| **Incremental** | Predictable | Lower | Moderate | Interactive apps |

### When NOT to Use GC

- **For real-time systems**: Use real-time GC or custom allocators
- **For memory-constrained**: Use manual memory management or arenas
- **For deterministic timing**: Avoid GC pauses; use pooling
- **For bare metal**: Use static allocation or custom allocators

### Complexity Analysis

- **Mark-Sweep**: O(n + m) where n = heap objects, m = marks
- **Copying**: O(n) where n = live objects
- **Generational**: O(n) for minor collections (young gen), full O(n) for major
- **Space overhead**: Forwarding pointers, remembered sets

### Limitations

- **Pause times**: Stop-the-world collectors cause latency spikes
- **Fragmentation**: Mark-sweep causes internal/external fragmentation
- **Overhead**: GC costs 5-20% CPU time typically
- **Weak references**: Need special handling for finalizers
- **Debugging**: Memory leaks harder to find ( GC bugs are subtle)
- **Portability**: GC depends on memory layout, pointer formats

## Assessment Criteria

A high-quality GC implementation should have:

| Criterion | What to Look For |
|-----------|------------------|
| **Correctness** | Never collects live objects |
| **Completeness** | Collects all unreachable objects |
| **Pause time** | Low latency (for real-time: <1ms) |
| **Throughput** | Minimal overhead on mutator |
| **Memory** | Efficient use of heap |
| **Scaling** | Works on multi-core |

### Quality Indicators

✅ **Good**: Correct, low pause, efficient
⚠️ **Warning**: Memory bloat, occasional pauses
❌ **Bad**: Collects live objects (memory corruption), doesn't terminate

## Research Tools & Artifacts

Real-world garbage collectors to study:

| System | Collector | Key Innovation |
|--------|-----------|---------------|
| **HotSpot JVM** | G1, ZGC, Shenandoah | Generational, low-latency |
| **Go runtime** | Mark-assisted | Concurrent marking |
| **OCaml** | Minor GC | Short pauses |
| **GraalVM** | Truffle GC | Metacircular |
| **Racket** | Ring GC | Incremental |
| **Haskell GHC** | Generational | Parallel collection |

### Academic/Research GCs

- **Immix** (Blackburn et al.) - High throughput
- **ZGC** (Oracle) - Sub-millisecond pauses
- **Shenandoah** (Red Hat) - Concurrent compaction
- **MMTk** (Oxford) - Memory management tool kit

## Research Frontiers

### 1. Concurrent GC
- **Goal**: Reduce pause times by running concurrently
- **Techniques**: Write barriers, dirty bits, concurrent marking
- **Papers**: "Garbage Collection in Java 11" (Google I/O)
- **Tools**: ZGC, Shenandoah, Go GC

### 2. Region-Based Allocation
- **Goal**: Region-based memory management
- **Techniques**: Regions with different lifetimes
- **Papers**: "Memory Management with Regions" (Gay & Aiken)
- **Application**: Rust's arena allocator

### 3. GC for Functional Languages
- **Goal**: Efficient for immutable data
- **Techniques**: Generational, incremental, persistent data structures
- **Papers**: "The Design of Cryptographic Applications"
- **Application**: Haskell, Clojure, OCaml

### 4. Real-Time GC
- **Goal**: Predictable pause times
- **Techniques**: Incremental, concurrent, hybrid
- **Papers**: "Real-Time Garbage Collection" (Lieberman & Hewitt)
- **Application**: Embedded systems, games

## Implementation Pitfalls

| Pitfall | Real Consequence | Solution |
|---------|-----------------|----------|
| **Missing roots** | Memory corruption | Trace all stack slots, globals |
| **Write barrier bugs** | Incorrect collection | Test with pinned objects |
| **Fragmentation** | Out of memory | Compaction or copying |
| **Pin handling** | Objects can't move | Handle specially |
| **Finalizers** | Memory leaks | Track finalizer queue |

### The "Write Barrier" Problem

Concurrent GC needs write barriers:

```c
// Write barrier for generational GC
void write_barrier(void* obj, void* field, void* new_value) {
    // If storing old->new ref and new is in older gen
    if (is_heap_object(new_value) && 
        generation(new_value) < generation(obj)) {
        // Remember this store for minor GC
        remember_set_add(obj);
    }
    // Perform actual write
    *field = new_value;
}
```

### The "Stack Scanning" Challenge

Must scan all threads' stacks:

```c
void scan_roots() {
    for (Thread* t = all_threads; t != NULL; t = t->next) {
        // Get stack boundaries
        void* stack_top = t->stack_top;
        void* stack_bottom = t->stack_bottom;
        
        // Scan stack for pointers
        for (void* p = stack_bottom; p < stack_top; p += sizeof(void*)) {
            void* obj = *p;
            if (is_heap_object(obj)) {
                mark(obj);
            }
        }
    }
}
```

This is why GC pause times vary with stack depth!
