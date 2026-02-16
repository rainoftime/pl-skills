---
name: refinement-type-checker
description: 'Implements refinement types with predicates. Use when: (1) Property
  verification, (2) Dependent types lite, (3) Contracts.'
version: 1.0.0
tags:
- type-systems
- refinement-types
- verification
- smt
difficulty: advanced
languages:
- python
- z3
dependencies:
- type-checker-generator
---

# Refinement Type Checker

Implements refinement types with logical predicates.

## When to Use

- Property verification
- Contract checking
- Dependent types lite
- Pre/post conditions

## What This Skill Does

1. **Refines types** - Add predicates to types
2. **Checks subtypes** - With predicate implications
3. **Verifies** - Using SMT solvers
4. **Infer** - Refinement inference

## Core Theory

```
Refinement Type:
  {x : T | P}    -- T with predicate P
  
  Examples:
    {x : Int | x > 0}     -- Positive integers
    {x : Int | x >= 0 && x < n}  -- Bounded
    (x : Int) -> {y : Int | y = x + 1}  -- Function
```

## Implementation

```python
import z3
from dataclasses import dataclass
from typing import Dict, Optional

@dataclass
class RefinementType:
    """Refinement type {x : base | pred}"""
    base: 'Type'
    var: str  # Variable name
    predicate: z3.BoolRef

@dataclass
class Type:
    """Base type"""
    pass

@dataclass
class TInt(Type):
    pass

@dataclass
class TFun(Type):
    domain: Type
    codomain: RefinementType

class RefinementChecker:
    """Check refinement types"""
    
    def __init__(self):
        self.solver = z3.Solver()
        self.env: Dict[str, RefinementType] = {}
    
    def check(self, expr: 'Expr', expected: RefinementType) -> bool:
        """Check expression has refinement type"""
        
        inferred = self.infer(expr)
        
        # Check subtyping: inferred <: expected
        return self.subtype(inferred, expected)
    
    def infer(self, expr: 'Expr') -> RefinementType:
        """Infer refinement type"""
        
        match expr:
            case Const(n):
                return RefinementType(
                    TInt(),
                    "x",
                    z3.Int('x') == n
                )
            
            case Var(x):
                return self.env.get(x, RefinementType(TInt(), "x", True))
            
            case BinOp('+', e1, e2):
                t1 = self.infer(e1)
                t2 = self.infer(e2)
                
                # Refine result
                return RefinementType(
                    TInt(),
                    "r",
                    z3.And(
                        t1.predicate,
                        t2.predicate,
                        z3.Int('r') == z3.Int('e1_val') + z3.Int('e2_val')
                    )
                )
            
            case If(cond, then, else_):
                # Branch on condition
                t_cond = self.infer(cond)
                t_then = self.infer(then)
                t_else = self.infer(else_)
                
                return RefinementType(
                    t_then.base,
                    "x",
                    z3.Or(
                        z3.And(t_cond.predicate, t_then.predicate),
                        z3.And(z3.Not(t_cond.predicate), t_else.predicate)
                    )
                )
    
    def subtype(self, sub: RefinementType, sup: RefinementType) -> bool:
        """Check sub <: sup"""
        
        # sub <: sup iff ∀x. sub.predicate → sup.predicate
        # (and base types compatible)
        
        self.solver.push()
        
        # Substitute: rename variables
        sub_pred = sub.predicate
        sup_pred = sup.predicate
        
        # Check: sub → sup
        self.solver.add(z3.Not(z3.Implies(sub_pred, sup_pred)))
        
        result = self.solver.check() == z3.unsat
        self.solver.pop()
        
        return result

# Example: List length
def list_length_example():
    """
    // Refined list type
    type List a = Nil | Cons a (List a)
    
    // Length function with refinement
    length : (xs : List a) -> {n : Int | n >= 0}
    length Nil = 0
    length (Cons _ xs) = 1 + length xs
    
    // Type guarantees:
    // - Result is non-negative
    // - Correct length
    """
    pass

# Example: Sorted list
def sorted_list_example():
    """
    // Sorted list
    SortedList : List Int -> Prop
    SortedList Nil = true
    SortedList (Cons x Nil) = true
    SortedList (Cons x (Cons y ys)) = x <= y && SortedList (Cons y ys)
    
    // Insertion sort returns sorted
    insertSort : (xs : List Int) -> {ys : List Int | SortedList ys}
    
    // Type guarantees sorted output
    """
    pass
```

## SMT Encoding

```python
class RefinementEncoder:
    """Encode refinements to SMT"""
    
    def encode_type(self, rtype: RefinementType) -> z3.Sort:
        """Encode refinement type"""
        
        # For Int refinements: Int
        # For more complex: uninterpreted sort
        return z3.Int
    
    def encode_predicate(self, rtype: RefinementType) -> z3.BoolRef:
        """Encode predicate"""
        
        return rtype.predicate
    
    def encode_subtype(self, sub: RefinementType, sup: RefinementType) -> z3.BoolRef:
        """Encode subtype check"""
        
        # ∀x. sub.pred(x) → sup.pred(x)
        x = z3.Int('x')
        
        return z3.ForAll(
            [x],
            z3.Implies(
                self.substitute(rtype.sub.predicate, x),
                self.substitute(rtype.sup.predicate, x)
            )
        )
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| **Refinement** | Add predicates to types |
| **Subtyping** | Predicate implication |
| **SMT** | Solve predicate constraints |
| **Liquid types** | Refinement + inference |

## Liquid Types

```
Liquid Type Inference:
  - Base type from Hindley-Milner
  - Refinement from predicate variables
  - Solve constraints from usage
  
  Example:
    length :: xs:[a] -> {v:Int | v = len xs}
    
    Constraints:
      length [] = {v | v = 0}
      length (y:ys) = {v | v = 1 + length ys}
```

## Tips

- Use SMT solvers
- Keep predicates simple
- Leverage type inference
- Consider liquid types

## Related Skills

- `dependent-type-implementer` - Dependent types
- `hoare-logic-verifier` - Hoare logic
- `symbolic-execution-engine` - Symbolic execution

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| **Freeman & Pfenning, "Refinement Types for ML"** | Original refinement types |
| **Rondon et al., "Liquid Types"** | Liquid types paper |
| **Pfenning, "Introduction to Refinement Types"** | Survey |
| **Vazou et al., "Liquid Haskell"** | Refinement types in Haskell |
| **Xi & Pfenning, "Dependent Types"** | DML paper |

## Tradeoffs and Limitations

### Refinement Type Approach Tradeoffs

| Approach | Pros | Cons |
|----------|------|------|
| **Liquid types** | Automatic inference | Limited expressiveness |
| **Full refinements** | Expressive | Hard to check |
| **Index types** | Dependent-like | Complex |

### When NOT to Use Refinement Types

- **For complex proofs**: Use full dependent types or Coq
- **For runtime checks**: Regular testing may be better
- **For unknown properties**: Can't express

### Complexity Considerations

- **SMT solving**: NP-hard in worst case
- **Type checking**: Can be expensive
- **Constraint solving**: Often fast in practice

### Limitations

- **Expressiveness**: Not full dependent types
- **SMT dependencies**: Requires solver
- **Undecidability**: Some checks undecidable
- **Error messages**: Hard to explain
- **Scalability**: Large constraints slow
- **Termination**: Can't prove termination
- **Quantifiers**: Limited support

## Research Tools & Artifacts

Refinement type tools:

| Tool | Language | What to Learn |
|------|----------|---------------|
| **Liquid Haskell** | Haskell | Refinement types |
| **F*** | F* | Verification |
| **Dafny** | Dafny | Refinement |

## Research Frontiers

### 1. Liquid Types
- **Approach**: Predicate inference

## Implementation Pitfalls

| Pitfall | Real Consequence | Solution |
|---------|-----------------|----------|
| **SMT timeouts** | Slow checking | Simplify predicates |
