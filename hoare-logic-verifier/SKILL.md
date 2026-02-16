---
name: hoare-logic-verifier
description: 'Verifies programs using Hoare logic. Use when: (1) Proving program correctness,
  (2) Designing verified software, (3) Verifying loop invariants.'
version: 1.0.0
tags:
- verification
- hoare-logic
- program-proving
- correctness
difficulty: intermediate
languages:
- python
- coq
- why3
dependencies:
- operational-semantics-definer
---

# Hoare Logic Verifier

Verifies program correctness using Floyd-Hoare logic.

## When to Use

- Proving program correctness
- Developing verified software
- Verifying loop invariants
- Static verification

## What This Skill Does

1. **Specifies contracts** - Pre/postconditions and loop invariants
2. **Generates verification conditions** - Formulas to prove
3. **Checks soundness** - Proves VCs are valid
4. **Handles loops** - Invariant inference

## Key Concepts

| Concept | Description |
|---------|-------------|
| **Precondition** | State before execution |
| **Postcondition** | State after execution |
| **Invariant** | True before/after each loop iteration |
| **Weakest precondition** | Minimal condition ensuring postcondition |
| **Verification condition** | Formula to prove for correctness |

## Verification Condition Generation

```
{P} while b do c {Q}

VCs:
1. P ⇒ I                    (initiation)
2. I ∧ b ⇒ wp(c, I)         (preservation)  
3. I ∧ ¬b ⇒ Q               (usefulness)
```

## Tips

- Start with simple programs, add complexity
- Always verify loop invariants manually first
- Use consequences to strengthen/weaken
- Consider using SMT solvers for complex conditions
- Handle division carefully (non-zero)

## Common Patterns

### Swap

```
{ x = a ∧ y = b }
t := x;
x := y;
y := t;
{ x = b ∧ y = a }
```

### Linear Search

```
{ ∃i. A[i] = k ∧ 0 ≤ i < n }
i := 0;
while i < n do
    if A[i] = k then break;
    i := i + 1
{ (i < n ⇒ A[i] = k) ∧ (i = n ⇒ ∀j. 0≤j<n ⇒ A[j] ≠ k) }
```

## Related Skills

- `separation-logician` - Heap verification
- `invariant-generator` - Automatic invariant inference
- `loop-termination-prover` - Prove termination

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| **Hoare, "An Axiomatic Basis for Computer Programming"** | Original Hoare logic paper (Turing Award) |
| **Apt & Olderog, "Verification of Programs"** | Comprehensive survey |
| **Floyd, "Assigning Meanings to Programs"** | Predecessor to Hoare logic |
| **Nielson & Nielson, "Hoare Logic"** | Formal treatment |
| **Gupta et al., "A Practical Guide to Design of C Programs"** | Verifiable C coding |

## Tradeoffs and Limitations

### Approach Tradeoffs

| Approach | Pros | Cons |
|----------|------|------|
| **Standard Hoare** | Simple, intuitive | Can't handle heap/pointers |
| **Separation Logic** | Handles pointers, heap | More complex |
| **Dynamic Logic** | Loops as formulas | Harder to use |

### When NOT to Use Hoare Logic

- **For concurrent programs**: Use concurrent separation logic
- **For pointer-heavy code**: Use separation logic instead
- **For automated verification**: Consider model checking
- **For large codebases**: Consider symbolic execution + testing

### Complexity Considerations

- **VC generation**: O(n) in program size
- **SMT solving**: Expensive for complex formulas; undecidable in general
- **Invariant inference**: NP-hard in general

### Limitations

- **Loop invariants**: Must be provided manually (undecidable to find)
- **Frame problem**: Hard to specify what doesn't change; use separation logic
- **Partial correctness**: Standard Hoare logic proves partial correctness (no termination)
- **Scalability**: Manual proof effort grows with program size
- **Concurrency**: Requires extensions (concurrent separation logic)

## Research Tools & Artifacts

Verification tools based on Hoare logic:

| Tool | Language | What to Learn |
|------|----------|---------------|
| **Dafny** | C#/Boogie | Verified programs |
| **Verifiable C (VST)** | Coq | C verification |
| **Frama-C** | C | Static analysis |
| **Why3** | Why3 | Verification platform |
| **ESC/Java** | Java | Extended Static Checking |
| **Spec#** | C# | Contract-based verification |

### Interactive Theorem Provers

- **Coq** - Proof assistant, VST for C
- **Isabelle/HOL** - General purpose
- **Lean** - Functional verification
- **Agda** - Dependent types

## Research Frontiers

### 1. Verification Condition Generation
- **Goal**: Automate proof effort
- **Approach**: Generate VCs, discharge with SMT
- **Papers**: "VCGen for Dummies" (various)
- **Tools**: Boogie, Why3

### 2. Loop Invariant Inference
- **Goal**: Automatically find invariants
- **Approach**: Abstract interpretation, learning
- **Papers**: "Invariant Generation" (Sankaranarayanan)
- **Tools**: Abstract interpretation tools

### 3. Separation Logic
- **Goal**: Handle heap and pointers
- **Approach**: Local reasoning, frame rule
- **Papers**: "Separation Logic" (O'Hearn, Reynolds)
- **Tools**: Verifiable C, Smallfoot

### 4. Concurrent Verification
- **Goal**: Verify concurrent programs
- **Approach**: Concurrent separation logic
- **Papers**: "Concurrent Separation Logic" (O'Hearn)
- **Tools**: Verifast, Grain

## Implementation Pitfalls

| Pitfall | Real Consequence | Solution |
|---------|-----------------|----------|
| **Wrong invariant** | Unsound proof | Verify each VC |
| **Missing frames** | Incomplete specs | Use separation logic |
| **Division by zero** | Runtime errors | Add precondition |
| **Overflow** | Unsoundness | Use bounded integers |

### The "Loop Invariant" Challenge

Finding invariants is undecidable:

```python
# What invariant proves this?
i = 0
sum = 0
while i < n:
    sum = sum + i
    i = i + 1

# Answer: sum = i*(i-1)/2

# Another valid invariant: 0 <= i <= n AND sum >= 0
# But this is too weak to prove final result!
```

This is why verification requires human insight!
