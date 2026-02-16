---
name: ffi-designer
description: "Design and implement Foreign Function Interfaces for calling code in other languages."
version: "1.0.0"
tags: [runtime, ffi, interop, pldi]
difficulty: advanced
languages: [c, rust, python, haskell]
dependencies: [llvm-backend-generator, type-checker-generator]
---

# FFI Designer

Foreign Function Interfaces (FFI) enable programs to call code written in other languages. They bridge language runtimes and enable reuse of existing libraries.

## When to Use This Skill

- Calling C libraries from high-level languages
- Interoperability between language runtimes
- Binding generation
- Performance-critical interop
- Embedding interpreters

## What This Skill Does

1. **Type Mapping**: Convert types between languages
2. **Calling Convention**: Handle ABI differences
3. **Memory Management**: Manage memory across boundaries
4. **Callback Support**: Allow foreign code to call back
5. **Error Handling**: Propagate exceptions across FFI

## Key Concepts

| Concept | Description |
|---------|-------------|
| ABI | Application Binary Interface |
| Calling Convention | How parameters are passed |
| Type Marshalling | Convert types across boundaries |
| Callback | Function pointer passed to foreign code |
| Binding | Glue code for FFI |

## Tips

- Use binding generators for large libraries
- Handle memory ownership carefully
- Document ownership semantics
- Test with sanitizers
- Consider thread safety

## Common Use Cases

- Calling C libraries
- System programming
- Performance-critical code
- Native GUI bindings
- Game engine integration

## Related Skills

- `llvm-backend-generator` - Generate FFI code
- `type-checker-generator` - Type-safe FFI
- `memory-allocator` - Memory management

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| ctypes documentation | Python FFI |
| JNI specification | Java Native Interface |
| "FFI and PL design" papers | Design principles |

## Tradeoffs and Limitations

### Approach Tradeoffs

| Approach | Pros | Cons |
|----------|------|------|
| ctypes | Simple, Python | Slow |
| cffi | Fast | More complex |
| Native bindings | Fastest | Language-specific |

### When NOT to Use This Skill

- Pure language code
- When performance isn't critical
- Cross-platform portability required

### Limitations

- ABI compatibility issues
- Platform-specific behavior
- Complex type mappings

## Assessment Criteria

A high-quality implementation should have:

| Criterion | What to Look For |
|-----------|------------------|
| Type Safety | Correct type mappings |
| Memory Safety | Proper ownership |
| Performance | Minimal overhead |
| Usability | Easy to use |

### Quality Indicators

✅ **Good**: Type-safe, handles memory correctly, clean API
⚠️ **Warning**: Some manual memory management needed
❌ **Bad**: Type-unsafe, memory leaks, crashes

## Research Tools & Artifacts

Real-world FFI systems:

| Tool | Why It Matters |
|------|----------------|
| **cffi (Python)** | C FFI for Python |
| **JNI** | Java Native Interface |
| **SWIG** | Simplified wrapper generator |
| **clang bindings** | LLVM-based FFI |

### Key Systems

- **GHC Haskell FFI**: Type-safe FFI
- **Rust FFI**: Safe FFI with ownership

## Research Frontiers

Current FFI research:

| Direction | Key Papers | Challenge |
|-----------|------------|-----------|
| **Safe FFI** | "Safe FFI" (2018) | Memory safety |
| **Zero-cost** | "Zero-cost FFI" | Performance |
| **Bidirectional** | "Foreign函" | Two-way interop |

### Hot Topics

1. **WebAssembly FFI**: Wasm FFI design
2. **Multi-language runtimes**: GraalVM polyglot

## Implementation Pitfalls

Common FFI bugs:

| Pitfall | Real Example | Prevention |
|---------|--------------|------------|
| **Memory leaks** | Not freeing native memory | Ownership rules |
| **Type mismatches** | Wrong ABI | Use bindings |
| **GC issues** | GC collected native pointer | Keep reference |
| **Encoding** | String encoding issues | Use proper encoding |
