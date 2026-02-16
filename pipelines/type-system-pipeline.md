---
name: type-system-pipeline
description: "End-to-end pipeline for implementing a type system from scratch."
version: "1.0.0"
skills:
  - simply-typed-lambda-calculus
  - type-checker-generator
  - type-inference-engine
  - bidirectional-type-checking
  - subtyping-verifier
---

# Type System Pipeline

This pipeline demonstrates implementing a complete type system for a programming language.

## Pipeline Steps

```
Language Spec → STLC Core → Type Checker → Inference → Subtyping → Advanced Features
```

## Step 1: Define Core Language (STLC)

**Skill**: `simply-typed-lambda-calculus`

**Input**: Language specification
**Output**: Core calculus with types

```python
# Define base types
types = {
    'Int': BaseType('Int'),
    'Bool': BaseType('Bool'),
    'Fun': lambda a, b: FunType(a, b)
}

# Define terms
terms = """
e ::= x | λx:τ.e | e e | n | true | false | if e then e else e
"""
```

## Step 2: Generate Type Checker

**Skill**: `type-checker-generator`

**Input**: Typing rules
**Output**: Type checker implementation

```python
# Define typing rules
rules = """
T-Var:  Γ(x) = τ
        ---------
        Γ ⊢ x : τ

T-Abs:  Γ, x:τ₁ ⊢ e : τ₂
        ------------------
        Γ ⊢ λx:τ₁.e : τ₁ → τ₂

T-App:  Γ ⊢ e₁ : τ₁ → τ₂    Γ ⊢ e₂ : τ₁
        --------------------------------
        Γ ⊢ e₁ e₂ : τ₂
"""

# Generate type checker
type_checker = generate_type_checker(rules)
```

## Step 3: Add Type Inference

**Skill**: `type-inference-engine`

**Input**: Untyped program
**Output**: Principal type

```python
# Implement Hindley-Milner inference
def infer_type(expr, env):
    """Infer the most general type."""
    
    # Generate fresh type variables
    # Collect constraints
    # Solve constraints via unification
    
    return principal_type

# Example
expr = "fn x => fn y => x"
type = infer_type(expr, {})
# Result: ∀αβ. α → β → α
```

## Step 4: Bidirectional Checking

**Skill**: `bidirectional-type-checking`

**Input**: Mixed annotations
**Output**: Type-checked program with better errors

```python
# Bidirectional type checking
def synth(expr, env):
    """Synthesize type from expression."""
    if isinstance(expr, Var):
        return env[expr.name]
    if isinstance(expr, App):
        fun_type = synth(expr.func, env)
        arg_type = check(expr.arg, fun_type.arg, env)
        return fun_type.result

def check(expr, expected, env):
    """Check expression has expected type."""
    if isinstance(expr, Lam):
        # Annotation provided: check body
        return check(expr.body, expected.result, 
                     env.extend(expr.param, expected.arg))
    else:
        # Synthesize and compare
        actual = synth(expr, env)
        return actual == expected
```

## Step 5: Add Subtyping

**Skill**: `subtyping-verifier`

**Input**: Types with subtyping relation
**Output**: Subtype checker

```python
# Add record subtyping
def is_subtype(t1, t2):
    """Check if t1 <: t2."""
    
    # Width: more fields ok
    if isinstance(t1, RecordType) and isinstance(t2, RecordType):
        for field, type in t2.fields.items():
            if field not in t1.fields:
                return False
            if not is_subtype(t1.fields[field], type):
                return False
        return True
    
    # Function: contravariant in arg, covariant in result
    if isinstance(t1, FunType) and isinstance(t2, FunType):
        return (is_subtype(t2.arg, t1.arg) and  # contravariant
                is_subtype(t1.result, t2.result))  # covariant
```

## Complete Example: Building a Type System

```python
class TypeSystemBuilder:
    """Build a complete type system for a language."""
    
    def __init__(self):
        self.base_types = {}
        self.type_constructors = {}
        self.typing_rules = []
        self.subtyping_rules = []
    
    def add_base_type(self, name):
        """Add a base type (Int, Bool, String)."""
        self.base_types[name] = BaseType(name)
    
    def add_type_constructor(self, name, kind):
        """Add type constructor (List, Option, etc.)."""
        self.type_constructors[name] = TypeConstructor(name, kind)
    
    def add_typing_rule(self, rule):
        """Add a typing rule."""
        self.typing_rules.append(rule)
    
    def build_type_checker(self):
        """Generate the type checker."""
        return TypeChecker(
            base_types=self.base_types,
            constructors=self.type_constructors,
            rules=self.typing_rules
        )
    
    def build_type_inferencer(self):
        """Generate the type inferencer."""
        return TypeInferencer(
            base_types=self.base_types,
            constructors=self.type_constructors
        )


# Usage
builder = TypeSystemBuilder()

# Add base types
builder.add_base_type('Int')
builder.add_base_type('Bool')
builder.add_base_type('String')

# Add type constructors
builder.add_type_constructor('List', Kind(Type, Type))
builder.add_type_constructor('Option', Kind(Type, Type))

# Build the system
type_checker = builder.build_type_checker()
type_inferencer = builder.build_type_inferencer()

# Type check a program
program = """
let double = fn(x: Int) -> Int { x + x };
let apply = fn(f: Int -> Int, x: Int) -> Int { f(x) };
apply(double, 42)
"""

result = type_checker.check(program)
print(f"Type: {result.type}")  # Int
```

## Extensions

- Add `dependent-type-implementer` for dependent types
- Add `refinement-type-checker` for refinement types
- Add `effect-type-system` for effect tracking
- Add `ownership-type-system` for ownership/borrowing
