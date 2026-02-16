---
name: capability-system
description: "Implement capability-based security for fine-grained access control and least privilege."
version: "1.0.0"
tags: [security, capabilities, access-control, oopsla]
difficulty: intermediate
languages: [rust, capability-calculus, python]
dependencies: [type-checker-generator, linear-type-implementer]
---

# Capability System

Capability-based security uses unforgeable tokens (capabilities) to represent authority. Instead of checking "who you are" (ACLs), it checks "what you hold" (capabilities), enabling fine-grained least privilege.

## When to Use This Skill

- Building secure operating systems
- Implementing sandboxing
- Designing least-privilege systems
- Distributed object systems
- Secure browsers (seL4, Capsicum)

## What This Skill Does

1. **Capability Tokens**: Unforgeable references to resources
2. **Authority Delegation**: Transfer capabilities between principals
3. **Attenuation**: Reduce capability powers
4. **Revocation**: Revoke delegated capabilities
5. **Confinement**: Restrict capability propagation

## Key Concepts

| Concept | Description |
|---------|-------------|
| Capability | Unforgeable token granting authority |
| Attenuation | Reduce capability permissions |
| Delegation | Transfer capability to another principal |
| Revocation | Invalidate capability and descendants |
| Confinement | Restrict capability propagation |
| Facet | Specific interface to an object |

## Tips

- Use unforgeable tokens (cryptographic or memory-safe references)
- Implement proper attenuation
- Consider revocation carefully (may be impossible without tracking)
- Use object capabilities for fine-grained control
- Log capability usage for auditing

## Common Use Cases

- Secure operating systems (seL4, Fuchsia)
- Browser sandboxing
- Distributed object systems
- Cloud access control
- IoT device security

## Related Skills

- `information-flow-analyzer` - Track information flow
- `linear-type-implementer` - Linear capabilities
- `sandbox-builder` - Use capabilities for sandboxing
- `ownership-type-system` - Ownership and capabilities

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| Levy "Capability-Based Computer Systems" | Classic text |
| Miller "Capability Myths Demolished" | Clarifies misconceptions |
| Shapiro et al. "EROS: A Capability System" | Practical system |

## Tradeoffs and Limitations

### Approach Tradeoffs

| Approach | Pros | Cons |
|----------|------|------|
| Pure capabilities | Composable, no ambient authority | Requires language support |
| Hybrid (ACL + caps) | Practical | Complex |
| Cryptographic caps | Distributed | Performance |

### When NOT to Use This Skill

- Simple access control needs
- When ACLs suffice
- Performance-critical paths (crypto overhead)

### Limitations

- Revocation is complex
- Confinement is hard
- Lost capabilities are hard to recover

## Assessment Criteria

A high-quality implementation should have:

| Criterion | What to Look For |
|-----------|------------------|
| Unforgeability | Capabilities cannot be forged |
| Attenuation | Permissions can be reduced |
| Delegation | Capabilities can be shared |
| Revocation | Capabilities can be revoked |

### Quality Indicators

✅ **Good**: Unforgeable, supports attenuation and revocation
⚠️ **Warning**: Forgery possible, no revocation
❌ **Bad**: No security guarantees

## Research Tools & Artifacts

Capability systems:

| System | What to Learn |
|--------|---------------|
| **EROS** | Capability OS |
| **CapROS** | Modern capability OS |
| **Fuchsia** | Capability-based |

## Research Frontiers

### 1. Distributed Capabilities
- **Goal**: Capabilities across trust boundaries
- **Approach**: Cryptographic capabilities

## Implementation Pitfalls

| Pitfall | Real Consequence | Solution |
|---------|-----------------|----------|
| **Forgery** | Security breach | Cryptographic seals |
