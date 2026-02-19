---
name: smt-solver-interface
description: "Interface with SMT solvers for automated reasoning about program correctness."
version: "1.0.0"
tags: [verification, smt, z3, popl]
difficulty: intermediate
languages: [python, c++, rust]
dependencies: [hoare-logic-verifier, model-checker]
---

# SMT Solver Interface

SMT (Satisfiability Modulo Theories) solvers combine SAT solving with decision procedures for theories like arrays, bitvectors, and arithmetic. They are essential tools for program verification and synthesis.

## When to Use This Skill

- Verifying program correctness
- Solving constraint problems
- Automated theorem proving
- Program synthesis
- Test generation

## What This Skill Does

1. **Constraint Encoding**: Translate program properties to SMT formulas
2. **Solver Invocation**: Call SMT solvers (Z3, CVC5, etc.)
3. **Model Extraction**: Get satisfying assignments
4. **Unsat Cores**: Identify conflicting constraints
5. **Incremental Solving**: Reuse solver state

## Key Concepts

| Concept | Description |
|---------|-------------|
| SAT | Boolean satisfiability |
| SMT | SAT + theories (arrays, bitvectors, etc.) |
| Theory | Decision procedure for specific domain |
| Model | Satisfying assignment |
| Unsat Core | Minimal unsatisfiable subset |

## Tips

- Use incremental solving for efficiency
- Choose appropriate theories for your domain
- Use quantifiers sparingly (expensive)
- Extract unsat cores for debugging
- Profile solver time for large problems

## Common Use Cases

- Program verification
- Test generation
- Program synthesis
- Configuration analysis
- Security analysis

## Related Skills

- `hoare-logic-verifier` - Uses SMT for verification
- `model-checker` - Alternative verification approach
- `symbolic-execution-engine` - Generates SMT constraints
- `refinement-type-checker` - SMT-based checking

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| **De Moura & Bjørner, "Z3: An Efficient SMT Solver" (TACAS 2008)** | Z3 paper |
| **Barrett & Tinelli, "Satisfiability Modulo Theories" (Handbook of Model Checking 2014)** | SMT overview |
| **Kroening & Strichman, "Decision Procedures: An Algorithmic Point of View" (Springer, 2016)** | Comprehensive book |

## Tradeoffs and Limitations

### Approach Tradeoffs

| Approach | Pros | Cons |
|----------|------|------|
| Z3 | Powerful, well-documented | Can be slow |
| CVC5 | Good for theories | Less common |
| Mono-solving | Simple | Not incremental |

### When NOT to Use This Skill

- Decidable problems (use specialized algorithms)
- When model checking is more appropriate
- Very large formulas (may not scale)

### Limitations

- Quantifiers can cause undecidability
- Non-linear arithmetic is hard
- Solver performance varies

## Assessment Criteria

A high-quality implementation should have:

| Criterion | What to Look For |
|-----------|------------------|
| Correctness | Sound encoding |
| Efficiency | Appropriate theory selection |
| Usability | Clear error messages |
| Robustness | Handles solver timeouts |

### Quality Indicators

✅ **Good**: Correct encoding, incremental solving, model extraction
⚠️ **Warning**: Incorrect encoding, no timeout handling
❌ **Bad**: Soundness bugs, crashes on large inputs

## Research Tools & Artifacts

Real-world SMT solvers:

| Tool | Why It Matters |
|------|----------------|
| **Z3** | Microsoft SMT solver |
| **CVC5** | SMT solver |
| **Boolector** | Bitvector solver |
| **Alt-Ergo** | Proof assistant |

### Key Solvers

- **Z3**: Production SMT
- **CVC5**: Research solver

## Research Frontiers

Current SMT research:

| Direction | Key Papers | Challenge |
|-----------|------------|-----------|
| **Arithmetic** | "Nonlinear SMT" | Reals |
| **Quantifiers** | "Quantifier Instantiation" | Automation |

### Hot Topics

1. **SMT for verification**: Program verification
2. **SMT for synthesis**: Program synthesis

## Implementation Pitfalls

Common SMT bugs:

| Pitfall | Real Example | Prevention |
|---------|--------------|------------|
| **Encoding** | Wrong encoding | Verify |
| **Timeout** | Solver timeout | Timeout |
