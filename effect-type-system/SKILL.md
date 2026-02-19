---
name: effect-type-system
description: 'Implements algebraic effect types. Use when: (1) Handling side effects,
  (2) Extensible effects, (3) Effect inference.'
version: 1.0.0
tags:
- type-systems
- effects
- side-effects
- monads
difficulty: intermediate
languages:
- python
- haskell
dependencies:
- type-checker-generator
---

# Effect Type System

Implements algebraic effect type system for tracking computations.

## When to Use

- Effect inference
- Handler design
- Extensible effects
- Effect polymorphism

## What This Skill Does

1. **Defines effects** - Algebraic effect signatures
2. **Tracks operations** - Effectful computations
3. **Handles effects** - Effect handlers
4. **Infers effects** - Effect inference

## Core Theory

```
Effect Signature:
  effect State: get : Unit → Int
              put : Int → Unit
  
Effect Type:
  Computation with effect set
  T => E   (T with effects E)
  
Handler:
  handle expr with
    return x => x
  | get(k) => ...
```

## Implementation

```python
from dataclasses import dataclass, field
from typing import Dict, List, Set, Optional

@dataclass
class EffectOp:
    """Effect operation"""
    effect: str
    name: str
    param_type: 'Type'
    return_type: 'Type'

@dataclass
class EffectSet:
    """Set of effects"""
    effects: Set[str] = field(default_factory=set)
    
    def union(self, other: 'EffectSet') -> 'EffectSet':
        return EffectSet(self.effects | other.effects)
    
    def empty(self) -> bool:
        return len(self.effects) == 0

@dataclass
class EffectType:
    """Type with effects"""
    result: 'Type'
    effects: EffectSet

@dataclass
class Type:
    """Base type"""
    pass

@dataclass
class TInt(Type):
    pass

@dataclass
class TString(Type):
    pass

@dataclass  
class TFun(Type):
    param: Type
    result: EffectType  # Function has effect type

class EffectChecker:
    """Check effect typing"""
    
    def __init__(self):
        self.effect_sigs: Dict[str, Dict[str, EffectOp]] = {}
        self.handlers: Dict[str, EffectType] = {}
    
    def declare_effect(self, name: str, ops: Dict[str, EffectOp]):
        """Declare effect signature"""
        self.effect_sigs[name] = ops
    
    def check(self, expr: 'Expr', env: Dict) -> EffectType:
        """Check expression effect type"""
        
        match expr:
            case Const(n):
                return EffectType(TInt(), EffectSet())
            
            case Var(x):
                return env[x]
            
            case Lambda(x, body):
                body_type = self.check(body, {**env, x: EffectType(TInt(), EffectSet())})
                return EffectType(
                    TFun(TInt(), body_type),
                    body_type.effects
                )
            
            case App(func, arg):
                func_type = self.check(func, env)
                arg_type = self.check(arg, env)
                
                if isinstance(func_type.result, TFun):
                    # Check effect handling
                    return func_type.result.result
                raise TypeError("Not a function")
            
            case Perform(effect, op, arg):
                # Perform effect operation
                if effect in self.effect_sigs:
                    op_sig = self.effect_sigs[effect].get(op)
                    if op_sig:
                        return EffectType(
                            op_sig.return_type,
                            EffectSet({effect})
                        )
                raise TypeError(f"Unknown effect operation: {effect}.{op}")
            
            case Handle(body, handler):
                # Handle effects in body
                body_type = self.check(body, env)
                
                # Check handler covers effects
                uncovered = body_type.effects.effects - set(handler.effects.keys())
                if uncovered:
                    raise TypeError(f"Unhandled effects: {uncovered}")
                
                # Handler produces pure result
                return EffectType(handler.return_type, EffectSet())
    
    def infer(self, expr: 'Expr', env: Dict) -> EffectType:
        """Infer effect type"""
        
        # Similar to check but with inference
        return self.check(expr, env)

# Example: State effect
def state_effect_example():
    """
    effect State:
      get : () -> Int
      put : Int -> ()
    
    let counter =
      handle
        let x = perform State.get() in
        perform State.put(x + 1);
        x
      with
        return x -> x
      | get(k) -> k(0)  -- handler provides state
      | put(n) -> k(())  -- handler continues
    
    Type: () => {State}
    """
    pass
```

## Effect Handlers

```python
@dataclass
class Handler:
    """Effect handler"""
    effect: str
    return_clause: 'Clause'  # return x => expr
    ops: Dict[str, 'Clause']  # op(k) => expr

class HandlerTypechecker:
    """Typecheck handlers"""
    
    def check_handler(self, handler: Handler, eff_type: EffectType) -> Type:
        """Check handler type"""
        
        # Check return clause type matches
        # Check each operation handler type
        for op_name, clause in handler.ops.items():
            # op(k) => body
            # k: T -> U where T is op param type
            # body must produce U
            pass
        
        return handler.return_clause.result_type
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| **Effect** | Observable computation |
| **Handler** | Handle effect operations |
| **Operation** | Effect primitive |
| **Resume** | Continue computation |

## Effect Inference

```python
class EffectInference:
    """Infer effects"""
    
    def infer_effects(self, expr: 'Expr') -> EffectSet:
        """Infer effect set"""
        
        # Collect effects
        effects = set()
        
        def visit(e):
            if isinstance(e, Perform):
                effects.add(e.effect)
            for child in e.children:
                visit(child)
        
        visit(expr)
        return EffectSet(effects)
```

## Tips

- Declare effect signatures
- Handle all effects
- Consider polymorphism
- Use handlers for I/O

## Related Skills

- `type-inference-engine` - Type inference
- `linear-type-implementer` - Linear types
- `effect-type-system` - Effects

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| **Plotkin & Pretnar, "Handlers of Algebraic Effects" (ESOP 2009)** | Foundational paper on effect handlers |
| **Bauer & Pretnar, "Programming with Algebraic Effects and Handlers" (J. LAMP, 2015)** | Effect handlers tutorial and the Eff language |
| **Kammar, Lindley, Oury, "Handlers in Action" (ICFP 2013)** | Popularized handlers with implementations |
| **Plotkin & Power, "Notions of Computation Determine Monads" (2002)** | Algebraic foundations of effects |
| **Leijen, "Koka: Programming with Row Polymorphic Effect Types" (MSFP 2014)** | Practical effect-typed language |

## Tradeoffs and Limitations

### Effect System Tradeoffs

| Approach | Pros | Cons |
|----------|------|------|
| **Row polymorphism** | Flexible | Complex inference |
| **Effect subscriptions** | Explicit | Verbose |
| **Implicit effects** | Convenient | Hard to track |

### When NOT to Use Effect Types

- **For simple programs**: Monads may be simpler
- **For IO-heavy code**: Direct IO may be clearer
- **For teaching**: Start with monads

### Complexity Considerations

- **Effect inference**: Can be complex
- **Handler composition**: Non-trivial
- **Polymorphism**: Requires care

### Limitations

- **Inference difficulty**: Effect inference hard
- **Handler complexity**: Multiple handlers complex
- **Error messages**: Hard to make clear
- **Performance**: Handler overhead
- **Interaction with exceptions**: Complex
- **Debugging**: Hard to trace effects
- **Tooling**: IDE support limited

## Research Tools & Artifacts

Real-world effect type systems:

| Tool | Why It Matters |
|------|----------------|
| **Koka** | Production effect-typed language |
| **Frank** | Effect handlers with inference |
| **Eff** | Effect language research |
| **Multicore OCaml** | Experimental effects |
| **Haskell** | Monad transformers for effects |

### Famous Effect Systems

- **Koka**: Microsoft effect language
- **Frank**:(handler f) -> T syntax

## Research Frontiers

Current effect system research:

| Direction | Key Papers | Challenge |
|-----------|------------|-----------|
| **Effect rows** | "Row Polymorphism" | Extensible effects |
| **Effect handlers** | "Handlers of Algebraic Effects" | Handler composition |
| **Effect inference** | "Inference for Effects" | Automating inference |

### Hot Topics

1. **Effects in Rust**: Effects RFC
2. **Effects in Python**: PEP proposal

## Implementation Pitfalls

Common effect system bugs:

| Pitfall | Real Example | Prevention |
|---------|--------------|------------|
| **Effect explosion** | Too many effects inferred | Polymorphism |
| **Wrong handler** | Wrong effect handled | Handler ordering |
| **Subeffecting** | Wrong subeffect relation | Check | rows
