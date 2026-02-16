---
name: property-based-tester
description: "Generates property-based tests that verify invariants across thousands of randomly generated inputs."
version: "1.0.0"
tags: [testing, verification, random-generation, property-testing]
difficulty: intermediate
languages: [haskell, ocaml, rust, python, scala]
dependencies: [type-inference-engine, smt-solver-interface]
---

# Property-Based Tester

Implements property-based testing frameworks that generate random test inputs and verify properties hold, finding edge cases that manual testing misses.

## When to Use This Skill

- Testing algebraic laws (monoid, functor, monad)
- Verifying compiler transformations preserve semantics
- Finding bugs in data structures
- Fuzzing APIs with type-aware generation

## What This Skill Does

1. **Generators**: Builds random generators for types via combinators
2. **Property Definition**: Defines properties as functions returning Boolean
3. **Shrinking**: Implements minimal counterexample finding
4. **Statistics**: Reports distribution of test inputs

## Key Concepts

| Concept | Description |
|---------|-------------|
| Generator | Produces random values of a type |
| Shrinker | Reduces failing inputs to minimal examples |
| Property | Invariant that should hold for all inputs |
| Coverage | Distribution of generated inputs |

## Tips

- Write properties that should always hold, not just examples
- Use shrinking to get minimal failing cases
- Cover edge cases: empty, single element, large inputs
- Combine with type-based generation for better coverage

## Related Skills

- `smt-solver-interface` - Symbolic verification
- `fuzzer-generator` - Random testing
- `type-inference-engine` - Type-aware generation

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| QuickCheck: Lightweight Automatic Testing | Original Haskell testing library |
| Hypothesis: Property-based testing in Python | Python ecosystem standard |
| Testing the Hard Stuff | Random testing for critical software |

## Tradeoffs and Limitations

| Approach | Pros | Cons |
|----------|------|------|
| Random generation | Finds edge cases | May miss specific bugs |
| Enumeration | Complete coverage | State space explosion |
| Symbolic execution | Targeted testing | Slower, complex |

## Assessment Criteria

| Criterion | What to Look For |
|-----------|------------------|
| Generator coverage | All interesting cases covered |
| Shrinking effectiveness | Minimal failing examples |
| Property correctness | Properties capture true invariants |

### Quality Indicators

✅ **Good**: Good coverage, effective shrinking, correct properties
⚠️ **Warning**: Limited coverage, slow shrinking
❌ **Bad**: Wrong properties, no shrinking

## Research Tools & Artifacts

Property-based testing frameworks:

| Tool | Language | What to Learn |
|------|----------|---------------|
| **QuickCheck** | Haskell | Original PBT |
| **Hypothesis** | Python | Python standard |
| **Fast-Check** | TypeScript | Composable |
| **ScalaCheck** | Scala | Integration |
| **Erlang QuickCheck** | Erlang | Industrial |

## Research Frontiers

### 1. Stateful Testing
- **Goal**: Test stateful systems
- **Papers**: "QuickCheck Testing for Stateful Software"
- **Tools**: StateMachines, sequences

## Implementation Pitfalls

| Pitfall | Real Consequence | Solution |
|---------|-----------------|----------|
| **Weak properties** | False positives | Strengthen invariants |
