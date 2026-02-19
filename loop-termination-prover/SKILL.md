---
name: loop-termination-prover
description: 'Proves loop termination using ranking functions. Use when: (1) Verifying
  programs, (2) Proving total correctness, (3) Program analysis.'
version: 1.0.0
tags:
- verification
- termination
- ranking-functions
- loops
difficulty: advanced
languages:
- python
- z3
- coq
dependencies:
- invariant-generator
---

# Loop Termination Prover

Proves loop termination using ranking functions.

## When to Use

- Program verification
- Total correctness
- Proving termination
- Formal methods

## What This Skill Does

1. **Analyzes loops** - Examines loop structure
2. **Finds rankings** - Discovers ranking functions
3. **Proves termination** - Shows decreasing bound
4. **Handles complexity** - Multiple paths, nested

## Key Concepts

| Concept | Description |
|---------|-------------|
| **Ranking function** | Decreases, bounded below |
| **Well-founded** | No infinite descending chains |
| **Lexicographic** | Tuple ordering |
| **Multiphase** | Multiple phases |

## Ranking Patterns

| Pattern | Ranking |
|---------|---------|
| `while i > 0 { i-- }` | i |
| `while i < n { i++ }` | n - i |
| `while i > 0 { j-- }` | i |
| Nested | Lexicographic |

## Tips

- Start with simple candidates
- Use SMT solvers for complex cases
- Consider multiple phases
- Handle recursion too

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| **Podelski & Rybalchenko, "A Complete Method for the Synthesis of Linear Ranking Functions" (VMCAI 2004)** | Linear ranking functions |
| **Bradley, Manna & Sipma, "Linear Ranking with Reachability" (CAV 2005)** | Termination proofs |
| **Cook et al., "Ranking Abstractions" (POPL 2006)** | Abstraction for termination |

## Related Skills

- `hoare-logic-verifier` - Hoare logic
- `invariant-generator` - Loop invariants
- `symbolic-execution-engine` - Symbolic execution

## Research Tools & Artifacts

Termination tools:

| Tool | What to Learn |
|------|---------------|
| **AProVE** | Termination prover |
| **Ctrl** | Termination checker |

## Research Frontiers

### 1. Complexity Analysis
- **Goal**: Derive complexity bounds

## Implementation Pitfalls

| Pitfall | Real Consequence | Solution |
|---------|-----------------|----------|
| **Non-termination** | Infinite loops | Find ranking |
