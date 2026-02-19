---
name: separation-logician
description: 'Verifies heap-manipulating programs using separation logic. Use when:
  (1) Proving memory safety, (2) Verifying pointer programs, (3) Analyzing data structures.'
version: 1.0.0
tags:
- verification
- separation-logic
- heap-reasoning
- memory-safety
difficulty: advanced
languages:
- python
- coq
- verifast
dependencies:
- hoare-logic-verifier
---

# Separation Logic Verifier

Verifies heap-manipulating programs using separation logic.

## When to Use

- Proving memory safety
- Verifying pointer/data structure code
- Analyzing concurrent programs
- Program certification

## What This Skill Does

1. **Defines heap logic** - Separating conjunction, points-to
2. **Specifies contracts** - Pre/post for heap operations
3. **Generates VCs** - Verification conditions for heap programs
4. **Handles framing** - Implicit frame inference

## Key Concepts

| Concept | Description |
|---------|-------------|
| **Separating conjunction** | * for disjoint heap |
| **Points-to** | x ↦ v for singleton heaps |
| **Frame rule** | Local reasoning, don't touch unrelated heap |
| **Local reasoning** | Verify in small footprint |
| **Small footprint** | Only specify accessed heap |

## Tips

- Use recursive predicates for data structures
- Apply frame rule to handle unmodified heap
- Consider SL → classical logic translation
- Use automatic provers (Smallfoot, Verifast)
- Handle arrays with array predicates

## Related Skills

- `hoare-logic-verifier` - Verify imperative programs
- `symbolic-execution-engine` - Symbolic execution
- `invariant-generator` - Infer loop invariants

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| **Reynolds, "Separation Logic: A Logic for Shared Mutable Data Structures" (LICS 2002)** | Foundational SL paper |
| **Ishtiaq & O'Hearn, "BI as an Assertion Language for Mutable Data Structures" (POPL 2001)** | Original SL paper |
| **O'Hearn, "Resources, Concurrency, and Local Reasoning" (2004)** | Concurrent separation logic |
| **Calcagno, O'Hearn & Yang, "Local Reasoning about a Copying Garbage Collector" (POPL 2004)** | SL for GC |
| **Birkedal et al., "Iris: Monoids and Invariants" (J. Formalized Reasoning 2016)** | Modern separation logic framework |

## Tradeoffs and Limitations

### SL Approach Tradeoffs

| Approach | Pros | Cons |
|----------|------|------|
| **Classical SL** | Simple, powerful | Hard to automate |
| **Bi-abductive** | Automatic | May lose precision |
| **Concurrent SL** | Handles concurrency | Complex |

### When NOT to Use Separation Logic

- **For functional code**: Standard Hoare logic may be simpler
- **For simple programs**: Overhead not justified
- **For automated tools**: May need external provers

### Complexity Considerations

- **Entailment checking**: Expensive; often undecidable
- **Predicate solving**: Complex for user-defined predicates
- **Space complexity**: Heap size matters

### Limitations

- **Automation**: Hard to automate entailment checking
- **Learning curve**: Requires understanding of local reasoning
- **Scalability**: Predicate libraries must scale
- **Concurrency**: Concurrent SL complex
- **Frame inference**: Must specify frame explicitly
- **Loop invariants**: Harder than standard Hoare

## Research Tools & Artifacts

Separation logic tools:

| Tool | Application | What to Learn |
|------|-------------|---------------|
| **Verifast** | C verification | Production SL |
| **Smallfoot** | Automatic SL | Original automatic |
| **Infer** | Facebook | Industrial analysis |
| **VST** | Coq | Verified C |
| **Iris** | Coq | Modern framework |

### Key Papers

- **O'Hearn** - Separation logic papers
- **Reynolds** - Foundational papers

## Research Frontiers

### 1. Concurrent Separation Logic
- **Goal**: Verify concurrent programs
- **Approach**: Concurrent views, invariants, ghost resources
- **Papers**: O'Hearn "Resources, Concurrency, and Local Reasoning" (2007)
- **Tools**: Iris, FCSL

### 2. Bi-Abduction
- **Goal**: Automatic frame inference
- **Approach**: Abductive reasoning for heap shapes
- **Papers**: Calcagno et al. "Compositional Shape Analysis" (2009)
- **Tools**: Infer (Facebook/Meta)

### 3. Iris
- **Goal**: Higher-order concurrent separation logic
- **Approach**: Step-indexed model, ghost state
- **Papers**: Jung et al. "Iris from the Ground Up" (2018)

## Implementation Pitfalls

| Pitfall | Real Consequence | Solution |
|---------|-----------------|----------|
| **Wrong framing** | Incomplete proofs | Use frame rule systematically |
| **Entailment undecidability** | Non-termination | Use approximations/heuristics |
| **Complex predicates** | Unreadable specs | Use abstraction layers |
| **Variable capture** | Wrong heap access | Use explicit names |
