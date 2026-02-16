---
name: subtyping-verifier
description: 'Verifies subtyping relations in type systems. Use when: (1) Implementing
  type systems, (2) Proving type safety, (3) Checking polymorphism.'
version: 1.0.0
tags:
- type-systems
- subtyping
- inheritance
- polymorphism
difficulty: intermediate
languages:
- python
- ocaml
dependencies:
- type-checker-generator
---

# Subtyping Verifier

Verifies subtyping relations in type systems.

## When to Use

- Implementing type systems
- Proving type safety
- Checking polymorphic code
- Formal verification

## What This Skill Does

1. **Defines subtyping rules** - Structural/nominal subtyping
2. **Checks relations** - Verify τ₁ <: τ₂
3. **Handles records** - Width/depth subtyping
4. **Proves transitivity** - Compose subtyping proofs

## Usage Example

```python
checker = SubtypingChecker()

# Int <: Int
assert checker.is_subtype(TInt(), TInt()) == True

# {x:Int, y:Int} <: {x:Int}  (width)
sub = TRecord({'x': TInt(), 'y': TInt()})
super_type = TRecord({'x': TInt()})
assert checker.is_subtype(sub, super_type) == True

# {x:Int} <: {x:Int, y:Int}  (NOT - missing field)
assert checker.is_subtype(super_type, sub) == False

# Function contravariance
# (Int → Bool) <: (Bool → Bool)
# Check: Bool <: Int (false), Bool <: Bool (true)
f1 = TFun(TInt(), TBool())
f2 = TFun(TBool(), TBool())
assert checker.is_subtype(f1, f2) == False

# (Bool → Bool) <: (Int → Bool)  
# Check: Int <: Bool (false), Bool <: Bool (true)
assert checker.is_subtype(f2, f1) == False

# Correct contravariance:
# (Bool → Int) <: (Int → Int)
# Check: Int <: Bool (false)3 = TFun - NO
f(TBool(), TInt())
f4 = TFun(TInt(), TInt())

# Correct: (Int → Bool) <: (Bool → Bool)?
# Dom: Bool <: Int? NO
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| **Width subtyping** | More fields allowed |
| **Depth subtyping** | Compatible field types |
| **Contravariance** | Function domain reversed |
| **Covariance** | Same direction as hierarchy |
| **Bivariance** | Both allowed (function results) |

## Tips

- Start with simple structural subtyping
- Add nominal when needed
- Handle recursion carefully
- Prove soundness alongside implementation

## Related Skills

- `type-checker-generator` - Type checking
- `type-inference-engine` - Type inference
- `hoare-logic-verifier` - Soundness proofs

## Research Tools & Artifacts

Subtyping in compilers:

| Tool | What to Learn |
|------|---------------|
| **Java** | Nominal subtyping |
| **TypeScript** | Structural subtyping |

## Research Frontiers

### 1. F-Bounded Polymorphism
- **Approach**: Self types

## Implementation Pitfalls

| Pitfall | Real Consequence | Solution |
|---------|-----------------|----------|
| **Transitivity** | Unsoundness | Prove lemmas |
