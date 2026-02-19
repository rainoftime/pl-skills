---
name: constant-propagation-pass
description: 'Implements constant propagation optimization. Use when: (1) Building
  compilers, (2) Learning program analysis, (3) Implementing optimizations.'
version: 1.0.0
tags:
- optimization
- compiler-pass
- dataflow
- constant-folding
difficulty: beginner
languages:
- python
- rust
dependencies:
- dataflow-analysis-framework
---

# Constant Propagation Pass

Implements dataflow constant propagation optimization.

## When to Use

- Building compilers
- Learning program analysis
- Implementing optimizations
- Static program analysis

## What This Skill Does

1. **Collects constants** - Tracks known values through the program
2. **Propagates** - Forward dataflow analysis with lattice operations
3. **Optimizes** - Replaces variables/expressions with constant values
4. **Handles conditionals** - Uses conditional branches to refine analysis

## Key Concepts

| Concept | Description |
|---------|-------------|
| **Lattice** | Partial order: ⊥ (uninitialized) < constants < ⊤ (unknown/NAC) |
| **Transfer function** | How statements transform lattice values |
| **Join** | Lattice meet at control flow merge points (∩ for constants) |
| **Worklist algorithm** | Iterative fixpoint computation |
| **Conditional sensitivity** | Using branch conditions to refine values |

## Lattice Structure

```
        ⊤ (NAC - Not A Constant)
       / | \
      1  2  3  ... (specific constants)
       \ | /
        ⊥ (UNDEF - Undefined)
```

## Tips

- Use join (∩) at control flow merge points
- Handle conservatively: unknown = NAC (not a constant)
- Consider arrays and pointers as killing definitions
- Combine with copy propagation for better results
- SSA form simplifies the analysis significantly

## Implementation

```python
from dataclasses import dataclass
from typing import Dict, Set, Optional
from enum import Enum

class ConstValue(Enum):
    UNDEF = 0   # Bottom: undefined
    NAC = 1     # Top: not a constant
    
@dataclass
class ConstantProp:
    lattice: Dict[str, any]  # var -> const value or UNDEF/NAC
    
    def transfer_assign(self, var: str, expr):
        if self.is_constant_expr(expr):
            self.lattice[var] = self.eval_const(expr)
        else:
            self.lattice[var] = ConstValue.NAC
    
    def join(self, v1, v2):
        if v1 == v2:
            return v1
        if v1 == ConstValue.UNDEF:
            return v2
        if v2 == ConstValue.UNDEF:
            return v1
        return ConstValue.NAC  # Different constants
```

## Related Skills

- `common-subexpression-eliminator` - CSE optimization
- `dead-code-eliminator` - Remove dead code after constant prop
- `dataflow-analysis-framework` - General dataflow infrastructure
- `ssa-constructor` - SSA form enables sparse constant propagation

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| **Wegman & Zadeck, "Constant Propagation with Conditional Branches" (TOPLAS 1991)** | Foundational sparse conditional constant propagation algorithm |
| **Cytron et al., "Efficiently Computing Static Single Assignment Form" (TOPLAS 1991)** | SSA construction enables efficient constant propagation |
| **Kildall, "A Unified Approach to Global Program Optimization" (POPL 1973)** | Original dataflow framework |

## Research Tools & Artifacts

Compiler optimization tools:

| Tool | What to Learn |
|------|---------------|
| **LLVM SCCP** | Sparse conditional constant propagation pass |
| **GCC SSA-CCP** | GCC's constant propagation implementation |

## Tradeoffs and Limitations

### Algorithm Tradeoffs

| Approach | Precision | Complexity | Use Case |
|----------|-----------|------------|----------|
| **Simple CP** | Low | O(n) | Quick pass |
| **Conditional CP** | Medium | O(n²) | Most compilers |
| **Sparse CP (SSA)** | Medium | O(n) | Modern compilers |
| **SCCP** | High | O(n) | Optimizing compilers |

### When NOT to Use

- **Interprocedural**: Need context-sensitive analysis
- **Pointers/aliasing**: May need pointer analysis first
- **Array elements**: Conservative handling required

## Implementation Pitfalls

| Pitfall | Real Consequence | Solution |
|---------|-----------------|----------|
| **Wrong join** | Imprecision or wrong results | Use correct lattice operations |
| **Uninitialized vars** | False constants | Track UNDEF properly |
| **Aliasing** | Wrong constant values | Conservative on pointers |
| **Loops** | Non-termination | Use worklist with widening |
