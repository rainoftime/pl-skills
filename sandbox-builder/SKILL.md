---
name: sandbox-builder
description: "Build secure sandboxes for isolating untrusted code execution."
version: "1.0.0"
tags: [security, sandboxing, isolation, oopsla]
difficulty: advanced
languages: [rust, c, python]
dependencies: [capability-system, ffi-designer]
---

# Sandbox Builder

Sandboxing isolates untrusted code execution, preventing it from affecting the host system. It's essential for browsers, plugin systems, and secure code execution platforms.

## When to Use This Skill

- Running untrusted code
- Browser plugin security
- Serverless function isolation
- Plugin architectures
- Multi-tenant systems

## What This Skill Does

1. **Isolation**: Separate untrusted code from host
2. **Resource Limits**: CPU, memory, time constraints
3. **System Call Filtering**: Restrict system calls
4. **Filesystem Namespacing**: Virtual filesystems
5. **Network Isolation**: Restrict network access

## Key Concepts

| Concept | Description |
|---------|-------------|
| Isolation | Separate execution environment |
| Resource Limits | CPU, memory, time constraints |
| Seccomp | Syscall filtering on Linux |
| Namespaces | Linux namespace isolation |
| Chroot | Change root directory |
| Virtualization | Full VM isolation |

## Tips

- Use multiple layers of defense
- Test with malicious inputs
- Log all violations
- Use established libraries when possible
- Consider OS-specific features

## Common Use Cases

- Browser sandboxes
- Serverless platforms
- Online code execution
- Plugin systems
- CI/CD pipelines

## Related Skills

- `capability-system` - Capability-based security
- `information-flow-analyzer` - Track information flow
- `ffi-designer` - Safe FFI boundaries
- `webassembly-runtime` - WASM sandboxing

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| Provos "Improving Host Security with System Call Policies" | Systrace/seccomp |
| Yee et al. "Native Client" | Chrome sandbox |
| seL4 documentation | Microkernel capabilities |

## Tradeoffs and Limitations

### Approach Tradeoffs

| Approach | Pros | Cons |
|----------|------|------|
| Seccomp | Lightweight | Linux only |
| Namespaces | Strong isolation | Complex |
| VMs | Complete isolation | Heavy |
| WASM | Portable | Limited APIs |

### When NOT to Use This Skill

- Trusted code execution
- When performance is critical
- Simple scripting needs

### Limitations

- OS-specific features
- Escape vulnerabilities exist
- Performance overhead

## Assessment Criteria

A high-quality implementation should have:

| Criterion | What to Look For |
|-----------|------------------|
| Isolation | Untrusted code cannot escape |
| Resource Limits | Enforced limits |
| Monitoring | Violations detected and logged |
| Performance | Reasonable overhead |

### Quality Indicators

✅ **Good**: Multiple isolation layers, proper limits, comprehensive logging
⚠️ **Warning**: Basic isolation, missing some limits
❌ **Bad**: Escape vulnerabilities, no resource limits

## Research Tools & Artifacts

Sandbox implementations:

| Tool | What to Learn |
|------|---------------|
| **Native Client** | Browser sandbox |
| **WebAssembly** | Sandboxed execution |
| **gvisor** | Container sandbox |

## Research Frontiers

### 1. Confidential Computing
- **Goal**: Hardware-based isolation
- **Approach**: SGX, TEEs

## Implementation Pitfalls

| Pitfall | Real Consequence | Solution |
|---------|-----------------|----------|
| **Escape bugs** | Security bypass | Defense in depth |
