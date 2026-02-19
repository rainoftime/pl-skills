---
name: invariant-generator
description: 'Infers loop invariants automatically. Use when: (1) Proving program
  correctness, (2) Automating verification, (3) Analyzing loops.'
version: 1.0.0
tags:
- verification
- invariants
- induction
- program-analysis
difficulty: advanced
languages:
- python
- z3
dependencies:
- abstract-interpretation-engine
---

# Invariant Generator

Automatically infers loop invariants for program verification.

## When to Use

- Proving program correctness
- Automating verification
- Loop analysis
- Counterexample generation

## What This Skill Does

1. **Analyzes loops** - Examines loop structure
2. **Infers candidates** - Generates invariant candidates
3. **Verifies** - Checks if invariant holds
4. **Refines** - Improves invariants

## Key Concepts

| Concept | Description |
|---------|-------------|
| **Loop invariant** | True before and after each iteration |
| **Initialization** | Holds initially |
| **Preservation** | Maintained by body |
| **Usefulness** | Helps prove postcondition |

## Techniques

- Template-based inference
- Abstract interpretation
- Counterexample-guided
- Iterative refinement

## Tips

- Start with simple bounds
- Handle accumulators carefully
- Use counterexamples to guide search
- Combine multiple techniques

## Related Skills

- `hoare-logic-verifier` - Verify with invariants
- `loop-termination-prover` - Prove termination
- `symbolic-execution-engine` - Symbolic execution

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| **Ernst et al., "The Daikon System for Dynamic Detection of Likely Invariants" (SCP 2007)** | Daikon invariant detector |
| **Sankaranarayanan et al., "Non-Linear Loop Invariant Generation using Gröbner Bases" (POPL 2004)** | Template-based invariant generation |
| **Csallner & Xie, "DynaMine: Finding Common Error Patterns by Mining Software Repositories" (ICSE 2005)** | Dynamic invariant mining |
| **Gulwani et al., "Generating Numerical Invariants with Polynomials" (POPL 2009)** | Counterexample-guided invariant generation |
| **Sharma & Aiken, "From Invariants to Code" (POPL 2014)** | Interpolants-based invariant generation |

## Tradeoffs and Limitations

### Invariant Inference Approach Tradeoffs

| Approach | Pros | Cons |
|----------|------|------|
| **Dynamic** | Precise, fast | May miss bugs |
| **Static** | Sound | Complex |
| **CEGAR** | Iterative refinement | May diverge |
| **Template** | Guided search | Template-dependent |

### When NOT to Use Automatic Invariant Inference

- **For simple loops**: Manual specification may be faster
- **For proving liveness**: Different techniques needed
- **For complex data structures**: Hard to infer

### Complexity Considerations

- **Template-based**: Exponential in template variables
- **Abstract interpretation**: Lattice height × program size
- **CEGAR**: May require many iterations

### Limitations

- **Completeness**: May miss important invariants
- **Precision**: May infer too weak or too strong
- **Scalability**: Hard for large programs
- **Template selection**: Must choose right templates
- **Arithmetic**: Nonlinear invariants hard
- **Data structures**: Complex invariants needed

## Research Tools & Artifacts

Invariant detection tools:

| Tool | What to Learn |
|------|---------------|
| **Daikon** | Dynamic invariants |
| **Armin** | Static invariants |

## Research Frontiers

### 1. CEGAR for Invariants
- **Approach**: Counterexample-guided

## Implementation Pitfalls

| Pitfall | Real Consequence | Solution |
|---------|-----------------|----------|
| **Weak invariants** | Failed proofs | Refine templates |
