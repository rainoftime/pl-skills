---
name: denotational-semantics-builder
description: 'Builds denotational semantic models. Use when: (1) Formalizing language
  semantics, (2) Proving program properties, (3) Semantic analysis.'
version: 1.0.0
tags:
- semantics
- denotational-semantics
- domain-theory
- pl-foundations
difficulty: advanced
languages:
- haskell
- coq
dependencies:
- operational-semantics-definer
---

# Denotational Semantics Builder

Constructs denotational semantic models for programming languages.

## When to Use

- Formal semantics definition
- Proving program properties
- Semantic equivalence
- Language design

## What This Skill Does

1. **Defines domains** - Semantic domains
2. **Maps syntax** - ⟦e⟧ : Exp → D
3. **Compositional** - Meaning from parts
4. **Handles recursion** - Fixed-point semantics

## Core Theory

```
Denotational Semantics:
  ⟦e⟧ ∈ D  where D is semantic domain
  
  ⟦n⟧ = ⟦n⟧ℤ ∈ ℤ
  ⟦x⟧ = ρ(x) ∈ D
  ⟦λx.e⟧ = λd. ⟦e⟧(ρ[x↦d])
  ⟦e₁ e₂⟧ = ⟦e₁⟧(⟦e₂⟧)
```

## Implementation

```python
from typing import Dict, Callable, Generic, TypeVar, Set
from dataclasses import dataclass
from functools import fixed_point

# Semantic domains
Domain = TypeVar('Domain')
Value = TypeVar('Value')

# Basic domains
class Int:
    """Integers"""
    def __init__(self, n: int):
        self.n = n

class Bool:
    """Booleans"""
    def __init__(self, b: bool):
        self.b = b

# Function domain
class Fun(Generic[Domain, Value]):
    """Function domain D → E"""
    def __init__(self, f: Callable[[Domain], Value]):
        self.f = f
    
    def apply(self, x: Domain) -> Value:
        return self.f(x)

# Product domain
class Prod(Generic[Domain, Value]):
    """Product domain D × E"""
    def __init__(self, first: Domain, second: Value):
        self.first = first
        self.second = second

# Environment
class Env(Dict[str, Value]):
    """Runtime environment"""
    pass

# Denotational semantics
class DenotationalSemantics:
    """Denotational semantics for simple language"""
    
    def __init__(self):
        self.functions = {}
    
    def sem_int(self, n: int) -> Int:
        """⟦n⟧ = n"""
        return Int(n)
    
    def sem_bool(self, b: bool) -> Bool:
        """⟦b⟧ = b"""
        return Bool(b)
    
    def sem_var(self, x: str, env: Env) -> Value:
        """⟦x⟧ = ρ(x)"""
        return env[x]
    
    def sem_lambda(self, x: str, body: 'Expr', env: Env) -> Value:
        """⟦λx.e⟧ = λd. ⟦e⟧(ρ[x↦d])"""
        
        def semantics(d: Value) -> Value:
            new_env = Env(env)
            new_env[x] = d
            return self.sem(body, new_env)
        
        return Fun(semantics)
    
    def sem_app(self, e1: 'Expr', e2: 'Expr', env: Env) -> Value:
        """⟦e₁ e₂⟧ = ⟦e₁⟧(⟦e₂⟧)"""
        
        v1 = self.sem(e1, env)
        v2 = self.sem(e2, env)
        
        return v1.apply(v2)
    
    def sem_if(self, cond: 'Expr', then: 'Expr', else_: 'Expr', env: Env) -> Value:
        """⟦if e then e₁ else e₂⟧"""
        
        v = self.sem(cond, env)
        
        if v.b:
            return self.sem(then, env)
        else:
            return self.sem(else_, env)
    
    def sem(self, expr: 'Expr', env: Env) -> Value:
        """Main semantics function"""
        
        match expr:
            case Int(n):
                return self.sem_int(n)
            
            case Bool(b):
                return self.sem_bool(b)
            
            case Var(x):
                return self.sem_var(x, env)
            
            case Lambda(x, body):
                return self.sem_lambda(x, body, env)
            
            case App(e1, e2):
                return self.sem_app(e1, e2, env)
            
            case If(cond, then, else_):
                return self.sem_if(cond, then, else_, env)
```

## Fixed-Point Semantics

```python
class RecursiveSemantics:
    """Semantics with recursion via fixed points"""
    
    def __init__(self):
        self.functions = {}
    
    def fix(self, F: Callable[['Value'], 'Value']) -> 'Value':
        """Fixed-point computation (Y combinator)"""
        
        # Simplified: use recursive function
        return fixed_point(F)
    
    def sem_letrec(self, x: str, e1: 'Expr', e2: 'Expr', env: Env) -> Value:
        """⟦letrec x = e₁ in e₂⟧"""
        
        # Create recursive environment
        def F(f):
            new_env = Env(env)
            new_env[x] = f
            return self.sem(e2, new_env)
        
        # Compute fixed point
        # This gives meaning to recursive definitions
        return self.fix(F)
    
    def sem_while(self, cond: 'Expr', body: 'Expr', env: Env) -> Value:
        """⟦while e do c⟧"""
        
        while True:
            v = self.sem(cond, env)
            if not v.b:
                return Bool(True)
            self.sem(body, env)
```

## Domain Theory

```python
class Domain:
    """Complete partial order"""
    
    def __init__(self):
        self.elements = set()
        self.partial_order = {}
    
    def lub(self, chain: Set['Value']) -> 'Value':
        """Least upper bound of chain"""
        # In complete partial order: lub of chain exists
        pass
    
    def bot(self) -> 'Value':
        """Bottom element (⊥)"""
        pass
    
    def le(self, x: 'Value', y: 'Value') -> bool:
        """Partial order (⊑)"""
        pass

# Lifted domains
class Lifted(Generic[Domain]):
    """Domain with bottom"""
    def __init__(self, d: Domain, bottom: Value):
        self.domain = d
        self.bottom = bottom

# Strict functions
class StrictFun(Domain):
    """Strict function (⊥ → ⊥ = ⊥)"""
    
    def __init__(self, dom: Domain, cod: Domain):
        self.domain = dom
        self.codomain = cod
    
    def apply(self, x: Value) -> Value:
        if x == self.domain.bottom:
            return self.codomain.bottom
        # Apply function
        pass
```

## Equivalence Proof

```python
class SemanticEquivalence:
    """Prove semantic equivalence"""
    
    def prove_eq(self, e1: 'Expr', e2: 'Expr') -> bool:
        """Prove ⟦e₁⟧ = ⟦e₂⟧"""
        
        # Compute denotations
        d1 = self.sem(e1, {})
        d2 = self.sem(e2, {})
        
        return d1 == d2
    
    def prove_extensional(self, e1: 'Expr', e2: 'Expr') -> bool:
        """
        Extensional equality:
        ∀ρ. ⟦e₁⟧ρ = ⟦e₂⟧ρ
        """
        
        # Test various environments
        test_envs = self.generate_test_envs()
        
        for env in test_envs:
            d1 = self.sem(e1, env)
            d2 = self.sem(e2, env)
            
            if d1 != d2:
                return False
        
        return True
```

## Denotational vs Operational

```
Operational:     How program executes (steps)
  ⟦e⟧ → v       (one step at a time)

Denotational:   What program means (mathematical)
  ⟦e⟧ ∈ D       (direct mapping)

Relationship:
  Operational → Denotational (adequacy)
  Denotational → Operational (full abstraction)
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| **Semantic domain** | Mathematical structure |
| **Compositional** | Meaning from parts |
| **Fixed point** | Recursion semantics |
| **Adequacy** | Operational ↔ Denotational |
| **Full abstraction** | Context equivalence |

## Tips

- Start with simple types
- Use domain theory for recursion
- Prove adequacy after
- Consider extensionality

## Related Skills

- `operational-semantics-definer` - Operational semantics
- `hoare-logic-verifier` - Axiomatic semantics
- `lambda-calculus-interpreter` - Lambda calculus

## Research Tools & Artifacts

Domain theory and denotational semantics tools:

| Resource | What to Learn |
|----------|---------------|
| **Stoy's "Denotational Semantics"** | The foundational text |
| **Winskel's "Formal Semantics"** | Domain theory for programmers |
| **Gunther's "Programming Language Semantics"** | Categorical perspective |
| **MLton** | Whole-program compiler with semantic analysis |

### Proof Assistant Formalizations

- **Coq stdlib** - Category theory, domain theory
- **Iris** - Higher-order separation logic
- **Cartesian Closed Categories** - Category theory for programming

## Research Frontiers

### 1. Game Semantics
- **Approach**: Programs as strategies in games
- **Advantage**: Captures sequential behavior precisely
- **Papers**: "Game Semantics" (Hyland & Ong, Abramsky et al.)
- **Application**: Full abstraction for PCF, verification

### 2. Relational Semantics
- **Approach**: Relations between programs
- **Advantage**: Proves relational properties
- **Papers**: "Relational Reasoning about Functions" (Benton et al.)
- **Application**: Program equivalence, refinement

### 3. Metric Semantics
- **Approach**: Programs as points in metric spaces
- **Advantage**: Quantitative reasoning
- **Papers**: "Metric Semantics" (de Bakker, America)
- **Application**: Probabilistic programs, bisimulation

### 4. Step-Indexed Semantics
- **Approach**: Stratified semantic definitions
- **Advantage**: Handles recursion and step counting
- **Papers**: "Step-Indexing" (Appel, McAllester)
- **Application**: Temporal logic, separation logic

## Implementation Pitfalls

| Pitfall | Real Consequence | Solution |
|---------|-----------------|----------|
| **Missing bottom element** | Non-termination not represented | Add ⊥ to all domains |
| **Non-continuous functions** | Fixed-point may not exist | Ensure monotonicity |
| **Wrong domain lift** | Strictness issues | Use strict function space |
| **Inadequate adequacy** | Semantics doesn't match behavior | Prove adequacy theorem |

### The "Fixed-Point Needs Continuity" Problem

Not all fixed-points compute correctly:

```python
# WRONG: Non-monotonic function
def F(f):
    if f(0) > 0: return lambda x. 0
    else: return lambda x. 1

# RIGHT: Monotonic function (for denotational)
# f is monotonic: if a ⊑ b then F(a) ⊑ F(b)
# Then Kleene fixed-point converges
```

### The "Adequacy Gap"

Operational and denotational semantics must match:

```
Denotational: ⟦e⟧ = ⊥  (doesn't terminate)
Operational:  e →* ⊥   (diverges)

Adequacy: If ⟦e⟧ = v then e →* v
          If ⟦e⟧ = ⊥ then e diverges (or gets stuck)
```
