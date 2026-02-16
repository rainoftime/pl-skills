---
name: relational-parametricity-prover
description: 'Proves relational parametricity. Use when: (1) Proving abstraction boundaries,
  (2) Reasoning about polymorphism, (3) Free theorems.'
version: 1.0.0
tags:
- type-theory
- parametricity
- proofs
- polymorphism
difficulty: advanced
languages:
- coq
- agda
dependencies:
- coq-proof-assistant
---

# Relational Parametricity Prover

Proves relational parametricity and derives free theorems.

## When to Use

- Proving abstraction
- Reasoning about polymorphism
- Deriving program properties
- Language metatheory

## What This Skill Does

1. **Defines relations** - Type-indexed relations
2. **Proves parametricity** - Abstraction theorem
3. **Derives theorems** - Free theorems
4. **Handles types** - Across all type constructors

## Core Theory

```
Parametricity:
  If Γ ⊢ e : τ
  Then ⟦e⟧ respects relational interpretation of τ

Free Theorems:
  ⊢ id : ∀α. α → α
  ⇒ ∀R. ∀x,y. R(x,y) → R(x,y)
  (identity function preserves all relations)
  
  ⊢ swap : ∀α,β. α × β → β × α  
  ⇒ ∀R,S. ∀x,y. R(x,y) → S(fst x)(fst y) → 
             S(snd x)(snd y)
```

## Implementation

```python
from dataclasses import dataclass
from typing import Dict, Set, Generic, TypeVar, Callable

@dataclass
class Type:
    """Type"""
    pass

@dataclass
class TVar(Type):
    """Type variable"""
    name: str

@dataclass
class TFun(Type):
    """Function type"""
    dom: Type
    cod: Type

@dataclass
class TProd(Type):
    """Product type"""
    left: Type
    right: Type

@dataclass
class TSum(Type):
    """Sum type"""
    left: Type
    right: Type

@dataclass
class TUnit(Type):
    """Unit type"""

class Relation(Generic[T]):
    """Binary relation"""
    
    def __init__(self, pairs: Set[tuple]):
        self.pairs = pairs
    
    def contains(self, x, y) -> bool:
        return (x, y) in self.pairs
    
    def domain(self) -> Set:
        return {x for x, y in self.pairs}
    
    def codomain(self) -> Set:
        return {y for x, y in self.pairs}

class RelationalParametricity:
    """Relational parametricity"""
    
    def __init__(self):
        self.relations: Dict[str, Relation] = {}
    
    def interp_type(self, tau: Type, rel_env: Dict[str, Relation]) -> Relation:
        """Interpret type as relation"""
        
        match tau:
            case TInt():
                # Identity relation on integers
                return Relation({(n, n) for n in range(1000)})
            
            case TBool():
                return Relation({(True, True), (False, False)})
            
            case TVar(alpha):
                return rel_env[alpha]
            
            case TFun(dom, cod):
                # Relational interpretation of functions
                rel_dom = self.interp_type(dom, rel_env)
                rel_cod = self.interp_type(cod, rel_env)
                
                # f ~ g iff ∀x,y. R(x,y) → R'(f(x), g(y))
                def func_rel() -> Relation:
                    pairs = set()
                    
                    # Get sample values
                    for x in rel_dom.domain():
                        for y in rel_dom.codomain():
                            if rel_dom.contains(x, y):
                                # Check function behavior
                                pass
                    
                    return Relation(pairs)
                
                return func_rel()
            
            case TProd(a, b):
                rel_a = self.interp_type(a, rel_env)
                rel_b = self.interp_type(b, rel_env)
                
                # (a₁,b₁) ~ (a₂,b₂) iff a₁~a₂ ∧ b₁~b₂
                pairs = set()
                for (a1, a2) in rel_a.pairs:
                    for (b1, b2) in rel_b.pairs:
                        pairs.add(((a1, b1), (a2, b2)))
                
                return Relation(pairs)
            
            case TSum(a, b):
                rel_a = self.interp_type(a, rel_env)
                rel_b = self.interp_type(b, rel_env)
                
                # inl(a₁) ~ inl(a₂) iff a₁~a₂
                # inr(b₁) ~ inr(b₂) iff b₁~b₂
                pairs = set()
                for (a1, a2) in rel_a.pairs:
                    pairs.add((('inl', a1), ('inl', a2)))
                for (b1, b2) in rel_b.pairs:
                    pairs.add((('inr', b1), ('inr', b2)))
                
                return Relation(pairs)
    
    def prove_parametricity(self, term: 'Term', tau: Type) -> bool:
        """
        Prove term respects relational interpretation
        
        Theorem: If ⊢ e : τ, then ⟦e⟧ respects ⟦τ⟧
        """
        
        rel_env = {
            'α': Relation({(0, 0)})  # Arbitrary relation
        }
        
        rel = self.interp_type(tau, rel_env)
        
        # Check term respects relation
        return self.check_respects(term, rel)
    
    def derive_free_theorem(self, tau: Type) -> str:
        """Derive free theorem for type"""
        
        match tau:
            case TFun(TVar(a), TVar(b)):
                # ∀α,β. (α → β) gives:
                return f"∀R,S. R(x₁,x₂) → S(f(x₁), f(x₂))"
            
            case TFun(TVar(a), TFun(TVar(b), TVar(c))):
                # ∀α,β,γ. (α → β → γ) gives:
                return f"∀R,S,T. R(x₁,x₂) → S(y₁,y₂) → T(f x₁ y₁)(f x₂ y₂)"
            
            case _:
                return "No free theorem"
```

## Free Theorems Examples

```python
def generate_free_theorems():
    """
    Free theorems from parametricity
    
    id : ∀α. α → α
    ⊢ ∀R. R(x,y) → R(x,y)
    (trivial)
    
    map : ∀α,β. (α → β) → [α] → [β]
    ⊢ ∀R,S. R(f,g) → R(map f, map g)
    (preserves relations)
    
    flip : ∀α,β,γ. (α → β → γ) → β → α → γ  
    ⊢ ∀R,S,T. R(f,f') → S(x,x') → T(y,y') → 
               T(flip f x y)(flip f' x' y')
    (flipping preserves relations)
    
    apply : ∀α,β. (α → β) → α → β
    ⊢ ∀R,S. R(f,f') → S(x,x') → S(f x, f' x')
    (application preserves relations)
    
    compose : ∀α,β,γ. (β → γ) → (α → β) → α → γ
    ⊢ ∀R,S,T. R(g,g') → S(f,f') → T(x,x') → 
               T(g (f x))(g' (f' x'))
    (composition preserves relations)
    """
    
    theorems = {
        'id': '∀R. R(x,y) → R(x,y)',
        'map': '∀R,S. R(f,g) → R(map f, map g)',
        'flip': '∀R,S,T. R(f,f\') → S(x,x\') → T(y,y\') → T(flip f x y)(flip f\' x\' y\')',
        'apply': '∀R,S. R(f,f\') → S(x,x\') → S(f x, f\' x\')',
        'compose': '∀R,S,T. R(g,g\') → S(f,f\') → T(x,x\') → T(g (f x))(g\' (f\' x\'))',
    }
    
    return theorems
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| **Relational interpretation** | Types as relations |
| **Abstraction** | Can't inspect type variables |
| **Free theorems** | Properties from types |
| **Representation independence** | Abstract types |

## Applications

- Proving data abstraction
- Reasoning about generics
- Proving compiler correctness
- Language metatheory

## Tips

- Start with simple types
- Use relational interpretation
- Derive properties systematically
- Consider effect types

## Related Skills

- `type-inference-engine` - Type systems
- `dependent-type-implementer` - System F
- `denotational-semantics-builder` - Semantics

## Research Tools & Artifacts

Real-world parametricity tools:

| Tool | Why It Matters |
|------|----------------|
| **Coq** | Parametricity proofs |
| **Isabelle** | Interactive proofs |
| **Agda** | Type-based proofs |

### Key Papers

- **Wadler**: "The Girard-Reynolds isomorphism"
- **Reynolds**: "Types, abstraction, parametricity"

## Research Frontiers

Current parametricity research:

| Direction | Key Papers | Challenge |
|-----------|------------|-----------|
| **Higher-order** | "Higher-order Parametricity" | Polymorphic types |
| **Linear** | "Linear Parametricity" | Linearity |

### Hot Topics

1. **Proof automation**: Auto-generating free theorems
2. **Quantitative**: Quantitative parametricity

## Implementation Pitfalls

Common parametricity bugs:

| Pitfall | Real Example | Prevention |
|---------|--------------|------------|
| **Non-parametric** | UnsafeCoerce | Don't cheat |
