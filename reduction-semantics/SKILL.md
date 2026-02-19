---
name: reduction-semantics
description: "Define program evaluation through rewrite rules and evaluation contexts."
version: "1.0.0"
tags: [semantics, interpreters, popl, theory]
difficulty: intermediate
languages: [haskell, racket, python]
dependencies: [lambda-calculus-interpreter, operational-semantics-definer]
---

# Reduction Semantics

Reduction semantics defines evaluation through rewrite rules on program terms, using evaluation contexts to specify evaluation order. It elegantly separates "where to reduce" from "what to reduce."

## When to Use This Skill

- Defining evaluation order precisely
- Implementing pattern-based rewriting
- Teaching programming language theory
- Building program transformers
- Reasoning about evaluation strategies

## What This Skill Does

1. **Evaluation Contexts**: Define where reduction can occur
2. **Reduction Rules**: Define what transformations apply
3. **Context Decomposition**: Split term into context + redex
4. **Plugging**: Place reduced term back in context
5. **Standard Reduction**: Define canonical evaluation sequence

## Key Concepts

| Concept | Description |
|---------|-------------|
| Evaluation Context | Position where reduction occurs |
| Redex | Reducible expression |
| Decomposition | Split term into context + redex |
| Plugging | Fill hole with term |
| Standard Reduction Sequence | Series of reductions to value |

## Tips

- Use Felleisen-style contexts for evaluation order
- Decomposition uniquely identifies next step
- Contexts encode evaluation strategy
- Use zippers for efficient context representation
- Pattern matching makes rules clear

## Common Use Cases

- Defining language semantics
- Implementing debuggers (show reduction steps)
- Type preservation proofs
- Building program transformers
- Teaching evaluation strategies

## Related Skills

- `lambda-calculus-interpreter` - Direct evaluation
- `abstract-machine` - Machine-based semantics
- `operational-semantics-definer` - Small-step semantics
- `program-transformer` - Rewrite-based transformation

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| **Felleisen & Hieb, "The Revised Report on the Syntactic Theories of Control" (1992)** | Evaluation contexts |
| **Wright & Felleisen, "A Syntactic Approach to Type Soundness" (1994)** | Type safety via contexts |
| **Plotkin, "Call-by-Name, Call-by-Value and the λ-Calculus" (1975)** | Evaluation strategies |
| **Barendregt, "The Lambda Calculus" (1984)** | Comprehensive λ-calculus reference |

## Tradeoffs and Limitations

### Approach Tradeoffs

| Approach | Pros | Cons |
|----------|------|------|
| Reduction semantics | Clear evaluation order | Requires context definition |
| Small-step operational | Simple transitions | More rules needed |
| Big-step operational | Fewer rules | No intermediate states |

### When NOT to Use This Skill

- When denotational semantics is preferred
- For simple languages without complex evaluation
- When performance is critical

### Limitations

- Context definition can be complex
- Harder to handle control operators
- Not as good for concurrency

## Assessment Criteria

A high-quality implementation should have:

| Criterion | What to Look For |
|-----------|------------------|
| Unique Decomposition | Each non-value has unique context+redex |
| Correct Plugging | plug(ctx, redex) = original term |
| Progress | Non-values always reduce |
| Preservation | Types preserved by reduction |

### Quality Indicators

✅ **Good**: Unique decomposition, correct evaluation order, handles all constructs
⚠️ **Warning**: Multiple possible decompositions, unclear evaluation order
❌ **Bad**: Decomposition fails for some terms, incorrect plugging

## Research Tools & Artifacts

Real-world reduction semantics tools:

| Tool | Why It Matters |
|------|----------------|
| **PLT Redex** | Semantic framework |
| **K framework** | Rewrite-based semantics |
| **Maude** | Rewriting logic |

### Key Systems

- **PLT Redex**: Racket semantics tool
- **K**: Semantic framework

## Research Frontiers

Current reduction semantics research:

| Direction | Key Papers | Challenge |
|-----------|------------|-----------|
| **Concurrent** | "Concurrent Rewriting" | Parallelism |
| **Stochastic** | "Stochastic RL" | Probabilistic |

### Hot Topics

1. **Mechanized semantics**: Coq/Lean reduction
2. **Wasm semantics**: WebAssembly reduction

## Implementation Pitfalls

Common reduction semantics bugs:

| Pitfall | Real Example | Prevention |
|---------|--------------|------------|
| **Non-unique** | Multiple redexes | Check determinism |
| **Wrong order** | Evaluation order | Verify strategy |
