---
name: information-flow-analyzer
description: "Analyze information flow through programs to enforce security policies and prevent data leaks."
version: "1.0.0"
tags: [security, taint, analysis, popl]
difficulty: advanced
languages: [java, python, rust]
dependencies: [taint-analysis, type-checker-generator]
---

# Information Flow Analyzer

Information flow analysis tracks how data flows through programs, enabling security policies like confidentiality (no leaks) and integrity (no corruption from untrusted sources).

## When to Use This Skill

- Enforcing data confidentiality
- Preventing information leaks
- Implementing taint tracking
- Security audits
- Building secure systems

## What This Skill Does

1. **Security Labels**: Assign security levels to data
2. **Flow Tracking**: Track how labels propagate
3. **Policy Enforcement**: Block disallowed flows
4. **Declassification**: Allow controlled release of secrets
5. **Implicit Flows**: Handle control-flow-based leaks

## Key Concepts

| Concept | Description |
|---------|-------------|
| Security Label | Classification level of data |
| Explicit Flow | Direct assignment of secret to public |
| Implicit Flow | Control-flow-based leak |
| Noninterference | Secret inputs don't affect public outputs |
| Declassification | Controlled release of secrets |
| Taint | Mark data from untrusted sources |

## Tips

- Handle implicit flows (control flow)
- Model declassification carefully
- Consider timing channels
- Test with both confidentiality and integrity
- Document security assumptions

## Common Use Cases

- Preventing data leaks
- Taint tracking in web apps
- Secure information systems
- Compliance (HIPAA, GDPR)
- Security audits

## Related Skills

- `taint-analysis` - Dynamic taint tracking
- `type-checker-generator` - Security type systems
- `capability-system` - Capability-based security
- `smt-solver-interface` - Verify security properties

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| Denning "A Lattice Model of Secure Information Flow" | Original paper |
| Volpano et al. "A Sound Type System for Secure Flow" | Type-based analysis |
| Sabelfeld, Myers "Language-Based Information-Flow Security" | Comprehensive survey |

## Tradeoffs and Limitations

### Approach Tradeoffs

| Approach | Pros | Cons |
|----------|------|------|
| Static typing | Compile-time | Conservative |
| Dynamic taint | Precise | Runtime overhead |
| Hybrid | Best of both | Complex |

### When NOT to Use This Skill

- When security is not a concern
- Performance-critical code
- When dynamic checks suffice

### Limitations

- Covert channels (timing, termination)
- Side channels
- Approximation may reject safe programs

## Assessment Criteria

A high-quality implementation should have:

| Criterion | What to Look For |
|-----------|------------------|
| Soundness | No information leaks |
| Implicit Flows | Handles control flow |
| Precision | Few false positives |
| Policy | Configurable security policy |

### Quality Indicators

✅ **Good**: Sound, handles implicit flows, configurable
⚠️ **Warning**: Misses implicit flows
❌ **Bad**: Allows explicit leaks, no policy support

## Research Tools & Artifacts

Real-world information flow tools:

| Tool | Why It Matters |
|------|----------------|
| **Jif** | Java information flow |
| **Flowlight** | Facebook's flow analysis |
| **SPARK** | Verified information flow |
| **Frama-C** | C information flow |
| **TaintDroid** | Android taint tracking |

### Key Systems

- **Jif**: Princeton's security-typed language
- **Flowlight**: Production taint analysis

## Research Frontiers

Current information flow research:

| Direction | Key Papers | Challenge |
|-----------|------------|-----------|
| **Dynamic** | "Dynamic Information Flow" | Precision |
| **Channels** | "Covert Channels" | Timing channels |
| **Quantitative** | "Quantitative IF" | Leakage amount |

### Hot Topics

1. **ML for information flow**: Learning flow patterns
2. **Differential privacy**: Quantitative leakage

## Implementation Pitfalls

Common information flow bugs:

| Pitfall | Real Example | Prevention |
|---------|--------------|------------|
| **Implicit flow** | Branch on secret | Track PC label |
| **Termination** | Loop count leaks | Non-terminating loops |
| **Timing** | Timing channel | Constant-time |
