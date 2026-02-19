---
name: dafny-verifier
description: "Use Dafny verification language for constructing verified programs with proofs."
version: "1.0.0"
tags: [verification, dafny, proofs, popl]
difficulty: intermediate
languages: [dafny]
dependencies: [hoare-logic-verifier, smt-solver-interface]
---

# Dafny Verifier

Dafny is a verification-aware programming language that supports writing specifications, programs, and proofs together. It compiles to verified code in multiple languages (C#, Java, Go, JavaScript).

## When to Use This Skill

- Writing verified programs
- Learning formal verification
- Proving algorithm correctness
- Teaching program proofs
- Developing certified software

## What This Skill Does

1. **Specification Writing**: Define pre/post conditions and invariants
2. **Verification**: Automatically verify programs against specs
3. **Lemma Proving**: Write and prove helper lemmas
4. **Termination**: Prove program termination
5. **Code Extraction**: Generate verified code

## Key Concepts

| Concept | Description |
|---------|-------------|
| Method | Executable code with specifications |
| Function | Mathematical function (pure, no side effects) |
| Lemma | Proof that can be called like a function |
| Invariant | Property that holds at loop header |
| Ensures | Postcondition specification |
| Requires | Precondition specification |

## Tips

- Start with strong specifications, weaken if needed
- Use lemmas to break complex proofs
- Write loop invariants before the body
- Use `calc` statements for calculation proofs
- The `old()` function refers to pre-state

## Common Use Cases

- Verified algorithms
- Certified libraries
- Teaching formal methods
- Security-critical code
- Protocol verification

## Related Skills

- `hoare-logic-verifier` - Theory behind Dafny
- `coq-proof-assistant` - More expressive proof assistant
- `smt-solver-interface` - Z3 powers Dafny
- `separation-logician` - For heap reasoning

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| **Leino, "Dafny: An Automatic Program Verifier for Functional Correctness" (LPAR 2010)** | Original Dafny paper |
| **Leino, "Program Proofs" (MIT Press, 2023)** | Comprehensive Dafny book |
| **Dafny documentation (dafny.org)** | Official reference |

## Tradeoffs and Limitations

### Approach Tradeoffs

| Approach | Pros | Cons |
|----------|------|------|
| Dafny | Automatic, usable | Limited expressiveness |
| Coq | Very expressive | Manual proofs |
| F* | More features | Steeper learning |

### When NOT to Use This Skill

- When proofs are not needed
- For low-level systems code (use Verus)
- When performance is critical

### Limitations

- Heap reasoning can be tricky
- Some proofs need explicit lemmas
- Not as expressive as Coq

## Assessment Criteria

A high-quality implementation should have:

| Criterion | What to Look For |
|-----------|------------------|
| Verification | All proofs check |
| Readability | Clear specifications |
| Modularity | Good lemma structure |
| Termination | All loops/functions terminate |

### Quality Indicators

✅ **Good**: All specs verified, clear invariants, modular lemmas
⚠️ **Warning**: Some specs need manual hints
❌ **Bad**: Unverified code, missing invariants

## Research Tools & Artifacts

Verification tools:

| Tool | Language | What to Learn |
|------|----------|---------------|
| **Verus** | Rust | Verified Rust |
| **F*** | F* | Verification |

## Research Frontiers

### 1. Automation
- **Goal**: More automatic proofs

## Implementation Pitfalls

| Pitfall | Real Consequence | Solution |
|---------|-----------------|----------|
| **Failed proofs** | Verification fails | Add lemmas |
