---
name: axiomatic-semantics
description: "Define program meaning through logical assertions and proof rules (Hoare logic)."
version: "1.0.0"
tags: [semantics, verification, popl, theory]
difficulty: intermediate
languages: [coq, why3, python]
dependencies: [hoare-logic-verifier, separation-logician]
---

# Axiomatic Semantics

Axiomatic semantics defines program meaning through logical assertions about program states. Hoare logic, the primary framework, uses triples {P} C {Q} meaning "if P holds before C, then Q holds after C terminates."

## When to Use This Skill

- Verifying program correctness
- Designing proof systems
- Teaching formal verification
- Specifying program behavior
- Building verification tools

## What This Skill Does

1. **Assertion Language**: Define predicates over program states
2. **Hoare Triples**: Specify pre/post conditions
3. **Proof Rules**: Derive correctness properties
4. **Weakest Precondition**: Compute necessary preconditions
5. **Loop Invariants**: Handle iteration constructs

## Key Concepts

| Concept | Description |
|---------|-------------|
| Hoare Triple | {P} C {Q} - precondition, command, postcondition |
| Weakest Precondition | Largest set of states guaranteeing Q after C |
| Loop Invariant | Property holding before, during, and after loop |
| Partial Correctness | If terminates, postcondition holds |
| Total Correctness | Terminates and postcondition holds |

## Tips

- Start with the postcondition, work backwards
- Find good loop invariants (the hard part)
- Use Z3 or other SMT solvers for implication checking
- Annotate loops with invariants explicitly
- Total correctness requires termination proofs

## Common Use Cases

- Verifying algorithm correctness
- Security proofs
- Compiler correctness
- Teaching formal methods
- Specification languages (JML, ACSL)

## Related Skills

- `hoare-logic-verifier` - Verification tool
- `separation-logician` - Memory reasoning
- `smt-solver-interface` - Automated proving
- `operational-semantics-definer` - Operational view

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| Hoare "An axiomatic basis for computer programming" (1969) | Original Hoare logic |
| Dijkstra "A Discipline of Programming" | Weakest preconditions |
| Winskel "The Formal Semantics of Programming Languages" | Comprehensive treatment |

## Tradeoffs and Limitations

### Approach Tradeoffs

| Approach | Pros | Cons |
|----------|------|------|
| Hoare Logic | Compositional, intuitive | Need loop invariants |
| Weakest Precondition | Automatic derivation | Complex expressions |
| Strongest Postcondition | Forward reasoning | Less compositional |

### When NOT to Use This Skill

- When operational semantics suffices
- For non-terminating programs (partial vs total)
- When automation is required (use model checking)

### Limitations

- Undecidable in general
- Requires loop invariant annotations
- No built-in concurrency reasoning (see separation logic)

## Assessment Criteria

A high-quality implementation should have:

| Criterion | What to Look For |
|-----------|------------------|
| Soundness | Proven triples are actually valid |
| Completeness | Valid triples can be proven |
| Automation | Uses SMT solver for implications |
| Expressiveness | Handles loops, procedures |

### Quality Indicators

✅ **Good**: Sound proof rules, handles loops, SMT integration
⚠️ **Warning**: Manual invariant annotation required
❌ **Bad**: Unsound rules, no loop support

## Research Tools & Artifacts

Real-world axiomatic semantics tools to study:

| Tool | Why It Matters |
|------|----------------|
| **Verifast** | Verified C programs with separation logic |
| **Frama-C (WP)** | Industrial-strength C verification |
| **Why3** | Platform for deductive verification |
| **OpenJML** | Java bytecode verification with JML |
| **Viper** | Verification framework with permission reasoning |
| **ACSL (Frama-C)** | ANSI/ISO C Specification Language |

### Key Verification Systems

- **Dafny**: Verifiable programs with inline proofs
- **F*** : Effectful verification with meta-theory
- **Coq**: Interactive proof with extraction to verified code
- **Isabelle/HOL**: Generic proof assistant

## Research Frontiers

Current active research in axiomatic semantics:

| Direction | Key Papers | Challenge |
|-----------|------------|-----------|
| **Automation** | "From Hoare Logic to Separation Logic" (2018) | Auto-generating loop invariants |
| **Fractional permissions** | "Fractional Permissions" (2010) | Concurrent read/write sharing |
| **Concurrent separation logic** | "Concurrent Separation Logic" (2004) | Verifying lock-free algorithms |
| **Iris** | "Higher-Order Ghost State" (2015) | Complex concurrency patterns |
| **Relational verification** | "Relational Hoare Logic" (2008) | Proving equivalence of programs |

### Hot Topics

1. **SMT integration**: Better theory support for arithmetic
2. **Horn clauses**: Automatic invariant generation
3. **Learning-based invariants**: Using ML to suggest invariants
4. **Quantum Hoare logic**: Verification for quantum programs

## Implementation Pitfalls

Common bugs in verification tools:

| Pitfall | Real Example | Prevention |
|---------|--------------|------------|
| **Missing frame rule** | Frama-C early versions | Explicit frame conditions |
| **Unsound loop invariant** | ESC/Java missing measures | Check variant/measure |
| **Weak memory** | Verifiers assuming sequential | Model weak memory explicitly |
| **Arithmetic overflow** | ACL2 unsoundness case | Bounded arithmetic support |
| **Aliasing bugs** | Missing permission checks | Always track permissions |
| **Incomplete theories** | Missing bitvector support | Cover all language features |

### The "Frame Rule" Bug

Early separation logic verifiers forgot the frame rule:
```c
// @requires P
// @ensures P * Q
void foo() {
    // Could lose Q if not framed!
}
```

**Solution**: Every rule now includes explicit frame conditions.

### Automation vs. Expressiveness Tradeoff

The core tension: more automation → less expressiveness:
- Full separation logic is undecidable
- Bi-abduction finds frame automatically (DISEL, etc.)
- Test generation supplements invariant inference
