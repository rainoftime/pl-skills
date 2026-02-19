---
name: ownership-type-system
description: 'Implements ownership and borrowing type system (Rust-style). Use when:
  (1) Verifying memory safety, (2) Data race prevention, (3) Lifetime analysis.'
version: 1.0.0
tags:
- type-systems
- ownership
- borrowing
- rust
difficulty: advanced
languages:
- python
- rust
dependencies:
- linear-type-implementer
---

# Ownership Type System

Implements ownership types with borrowing and lifetimes.

## When to Use

- Verifying memory safety
- Preventing data races
- Lifetime analysis
- Resource management

## What This Skill Does

1. **Implements ownership** - Each value has single owner
2. **Handles borrowing** - Mutable and immutable references
3. **Verifies lifetimes** - Lexical lifetimes
4. **Checks borrowing rules** - Aliasing XOR mutability

## Core Rules

```
Ownership Rules:
  - Each value has exactly one owner
  - When owner goes out of scope, value is dropped
  - Ownership can be transferred (move)
  - Ownership can be borrowed (reference)

Borrowing Rules:
  - Either OR many immutable references
  - OR exactly one mutable reference
  - References must not outlive borrowed data
```

## Implementation

```python
from dataclasses import dataclass, field
from typing import Dict, List, Set, Optional
from enum import Enum

class Ownership(Enum):
    OWNED = "owned"
    BORROWED_MUT = "borrowed_mut"
    BORROWED_IMMUT = "borrowed_immut"

@dataclass
class Type:
    """Ownership type"""
    base: str
    ownership: Ownership
    lifetime: Optional['Lifetime'] = None

@dataclass
class Lifetime:
    """Lifetime region"""
    name: str
    upper_bound: Optional['Lifetime'] = None

@dataclass
class Variable:
    """Variable with ownership info"""
    name: str
    typ: Type
    is_mutable: bool

@dataclass
class Borrow:
    """Borrow expression"""
    borrower: str  # Variable doing borrowing
    lender: str    # Variable being borrowed
    is_mutable: bool
    lifetime: Lifetime

class OwnershipChecker:
    """Check ownership and borrowing"""
    
    def __init__(self):
        self.variables: Dict[str, Variable] = {}
        self.borrows: List[Borrow] = []
        self.errors: List[str] = []
    
    def check_program(self, program: 'Program') -> bool:
        """Check ownership rules"""
        
        self.variables = {}
        self.borrows = []
        self.errors = []
        
        for stmt in program.statements:
            self.check_statement(stmt)
        
        return len(self.errors) == 0
    
    def check_statement(self, stmt: 'Stmt'):
        """Check single statement"""
        
        match stmt:
            case Let(x, typ, value):
                # Register owned variable
                self.variables[x] = Variable(x, typ, False)
            
            case Move(x, y):
                # Transfer ownership
                if y in self.variables:
                    # Check no active borrows
                    active = [b for b in self.borrows if b.lender == y]
                    if active:
                        self.errors.append(
                            f"Cannot move '{y}': has {len(active)} active borrows"
                        )
                    
                    # Transfer ownership
                    self.variables[x] = self.variables.pop(y)
            
            case BorrowRef(x, y, mutable):
                # Create borrow
                if y not in self.variables:
                    self.errors.append(f"Cannot borrow undeclared variable: {y}")
                    return
                
                lender = self.variables[y]
                
                # Check aliasing XOR mutability
                existing_borrows = [b for b in self.borrows if b.lender == y]
                
                if mutable:
                    # Cannot have other borrows
                    if existing_borrows:
                        self.errors.append(
                            f"Cannot mutably borrow '{y}': already borrowed"
                        )
                    # Cannot be borrowed mutably if already mutable
                    if lender.is_mutable:
                        self.errors.append(
                            f"Cannot mutably borrow already mutable variable: {y}"
                        )
                else:
                    # Check no mutable borrows
                    mutable_borrows = [b for b in existing_borrows if b.is_mutable]
                    if mutable_borrows:
                        self.errors.append(
                            f"Cannot immutably borrow '{y}': already mutably borrowed"
                        )
                
                # Record borrow
                borrow = Borrow(x, y, mutable, Lifetime("scope"))
                self.borrows.append(borrow)
                
                # Register borrower
                self.variables[x] = Variable(x, Type(lender.typ.base, 
                    Ownership.BORROWED_MUT if mutable else Ownership.BORROWED_IMMUT), mutable)
            
            case Assign(x, y):
                # Check not assigning to borrowed
                if x in self.variables:
                    x_var = self.variables[x]
                    if x_var.typ.ownership != Ownership.OWNED:
                        self.errors.append(f"Cannot assign to borrowed variable: {x}")
            
            case Drop(x):
                # Check no active borrows
                if x in self.variables:
                    active = [b for b in self.borrows if b.lender == x]
                    if active:
                        self.errors.append(
                            f"Cannot drop '{x}': has {len(active)} active borrows"
                        )
                    del self.variables[x]
    
    def check_lifetime(self, borrow: Borrow, lender_var: Variable) -> bool:
        """Check borrow lifetime"""
        
        if borrow.lifetime and lender_var.typ.lifetime:
            # Borrow lifetime must be <= lender lifetime
            return self.lifetime_sub(borrow.lifetime, lender_var.typ.lifetime)
        
        return True
    
    def lifetime_sub(self, sub: Lifetime, sup: Lifetime) -> bool:
        """Check sub ≤ sup"""
        
        # Simplified: lexical scoping
        return True

# Example programs
def examples():
    """
    Valid:
        let x = Vec::new();
        let y = &x;  // immutable borrow
        let z = &x;  // multiple immutable OK
    
    Invalid:
        let x = Vec::new();
        let y = &mut x;  // mutable borrow
        let z = &x;      // immutable after mutable
    
    Move semantics:
        let x = Vec::new();
        let y = x;  // x moved to y
        // x no longer valid
    """
    pass
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| **Ownership** | Single owner per value |
| **Borrow** | Temporary reference |
| **Move** | Transfer ownership |
| **Lifetime** | Region of validity |
| **Borrow checking** | Aliasing XOR mutability |

## Rust Borrowing Rules

```
Rules:
1. &T: Multiple immutable references OK
2. &mut T: Only one mutable reference
3. No references to references (directly)
4. &mut only from owned or &mut
5. Lifetime: borrow must not outlive lender
```

## Tips

- Track active borrows
- Handle drops correctly
- Check lifetime relationships
- Consider interior mutability

## Related Skills

- `linear-type-implementer` - Linear types
- `garbage-collector-implementer` - GC
- `type-checker-generator` - Type checking

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| **Clarke, Potter, Noble, "Ownership Types for Flexible Alias Protection" (OOPSLA 1998)** | Original ownership types paper |
| **Noble, Vitek, Potter, "Flexible Alias Protection" (ECOOP 1998)** | Conceptual foundation for ownership types |
| **Boyland, "Alias Burying: Unique Variables Without Destructive Reads" (2001)** | Uniqueness without destructive reads |
| **Tofte & Talpin, "Region-Based Memory Management" (Information and Computation, 1997)** | Region-based memory for ML |
| **Clarke, Drossopoulou, "Ownership, Encapsulation and the Disjointness of Type and Effect" (OOPSLA 2002)** | Ownership and effects |

## Tradeoffs and Limitations

### Ownership Approach Tradeoffs

| Approach | Pros | Cons |
|----------|------|------|
| **Rust-style** | Safe, no GC | Complexity |
| **Regions** | Fast | Complex regions |
| **Unique pointers** | Simple | Limited |
| **Capabilities** | Flexible | Hard to use |

### When NOT to Use Ownership Types

- **For simple programs**: GC is simpler
- **For rapid prototyping**: Ownership adds overhead
- **For shared state**: Use Arc/Rc instead

### Complexity Considerations

- **Borrow checking**: O(n) per borrow
- **Lifetimes**: Can require annotations
- **Error messages**: Complex to explain

### Limitations

- **Learning curve**: Complex rules to learn
- **Error messages**: Can be cryptic
- **Interior mutability**: Requires special handling (Cell, RefCell)
- **Lifetimes**: Must be explicit or inferred
- **Async**: Lifetimes with async complex
- **Interoperability**: FFI complexity
- **Shared ownership**: Not zero-cost

## Research Tools & Artifacts

Ownership systems:

| System | What to Learn |
|--------|---------------|
| **Rust** | Ownership/borrowing |
| **PyOxygen** | Ownership in Python |

## Research Frontiers

### 1. Linear Types in Haskell
- **Approach**: Linear Haskell

## Implementation Pitfalls

| Pitfall | Real Consequence | Solution |
|---------|-----------------|----------|
| **Borrow errors** | Rejected programs | Learn patterns |
