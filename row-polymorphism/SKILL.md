---
name: row-polymorphism
description: 'Implements row polymorphism for extensible records and variants. Use
  when: (1) Building languages with records, (2) Implementing object systems, (3)
  Type-safe database queries.'
version: 1.0.0
tags:
- type-systems
- row-polymorphism
- records
- extensibility
difficulty: intermediate
languages:
- python
- ocaml
dependencies:
- type-inference-engine
---

# Row Polymorphism

## When to Use

- Building extensible records/variants without nominal inheritance
- Designing effect rows or capability rows
- Implementing structural extensibility with type inference

## What This Skill Does

1. Models open rows with row variables
2. Defines row unification and row constraints
3. Supports record extension/projection typing
4. Explains tradeoffs for disjoint vs non-disjoint row systems

## How to Use

1. Represent rows as ordered/canonical label maps plus a tail variable
2. Define row unification with occurs checks on row variables
3. Enforce label constraints during extension/projection
4. Add diagnostics for missing labels and ambiguous row constraints

## Role Definition

You are a **row polymorphism expert** specializing in polymorphic record and variant types. You understand the theory of row types, extensible records, duplicate labels, and the connection to type inference and object systems.

## Core Expertise

### Theoretical Foundation
- **Row types**: Type-level lists of label-type pairs
- **Extensible records**: Open record types with row variables
- **Duplicate labels**: Allowing repeated field names (with unification)
- **Row extension**: Adding fields to rows
- **Row constraint solving**: Unifying rows with constraints

### Technical Skills

#### Row Type Representation

```haskell
-- Row as type-level list
type Row = [(Label, Type)]

-- Row variable (unification variable for rows)
type RowVar = ρ

-- Closed vs open rows
{ x: Int, y: Int }        -- closed row
{ x: Int | ρ }            -- open row (extensible)
{ x: Int | ρ where x:Int } -- constrained
```

#### Row Polymorphism in Practice

##### Record Types
```haskell
-- Polymorphic function over records with 'name' field
getName :: { name: String | ρ } → String
getName r = r.name

-- Extension
addAge :: { name: String | ρ } → Int → { name: String, age: Int | ρ }
addAge r age = { r | age }
```

##### Label Operations
```haskell
-- Delete field
delete :: Label l → { l: a | ρ } → { | ρ }

-- Rename
rename :: Label l → Label l' → { l: a | ρ } → { l': a | ρ }

-- Duplicate/override
override :: { l: a | ρ } → a → { l: a | ρ }
```

### Row Constraint Solving

| Constraint | Meaning |
|------------|---------|
| `ρ ⊇ { x: Int }` | Row ρ has at least x:Int |
| `ρ₁ = ρ₂` | Rows unify |
| `ρ = {}` | Empty row |
| `ρ = { x: Int | ρ' }` | Extend row |

### Implementation Approaches

| Approach | Description | Examples |
|----------|-------------|----------|
| **Record of functions** | Encode behavior as record fields | Object encodings |
| **Dictionary passing** | Pass row as implicit dictionary | OCaml objects |
| **Type-level computation** | Rows as type-level lists | Haskell |

### Advanced Row Features

#### Duplicate Labels (Disjoint or Non-Disjoint)
```haskell
-- Disjoint (each label at most once)
{ x: Int, x: String }  -- illegal in disjoint

-- Non-disjoint (multiple occurrences)
{ x: Int, x: Int }     -- merge to { x: Int }
{ x: Int, x: String }   -- union to { x: Int | x: String }
```

#### Rows with Kinds
```haskell
-- Label-level polymorphism
type Label = ∀ ρ. { get: a | ρ } → a

-- Field constraints
{ x: Int | a }  -- "a is row containing x:Int"
```

## Applications

| Domain | Application |
|--------|-------------|
| **Extensible records** | Dynamic records, configuration |
| **Object systems** | OOP without classes |
| **Variant types** | Sum types with named constructors |
| **Type-level programming** | Type-level maps/sets |
| **Generic programming** | Row-based generic deriving |

## Quality Criteria

Your row polymorphism implementations must:
- [ ] **Extensibility**: Functions work with extended records
- [ ] **Subtyping**: Structural subtyping via rows
- [ ] **Label scoping**: Proper handling of label shadowing
- [ ] **Unification**: Correct row constraint solving
- [ ] **Efficiency**: No runtime overhead for polymorphism

## Common Patterns

### Method Dispatch via Rows
```haskell
-- Object as record of methods
type Object = { 
  draw: Canvas → IO (),
  update: State → State 
}

-- Method lookup
draw :: Object → Canvas → IO ()
draw obj = obj.draw
```

### Extensible Effects
```haskell
-- Effects as row of handlers
type Eff = Reader Int | Writer String | State Bool

run :: Eff a → IO a  -- row unification
```

## Output Format

For row polymorphism tasks, provide:
1. **Row type syntax**: How rows are represented
2. **Constraint solving**: Unification rules
3. **Example programs**: Polymorphic record functions
4. **Type derivations**: Show row constraints
5. **Implementation**: Key algorithms

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| **Wand, "Type Inference for Objects"** | Row polymorphism origins |
| **Gaster & Jones, "A Polymorphic Type System for Extensible Records"** | Extended records |
| **Rémy, "Type Inference for Records"** | Comprehensive treatment |
| **Rémy, "Typing Record Concatenation for Free"** | Record concatenation and row-style typing |
| **Leijen, "Extensible Records"** | Practical row types |

## Tradeoffs and Limitations

### Row Type Approach Tradeoffs

| Approach | Pros | Cons |
|----------|------|------|
| **Disjoint** | Simple | Less expressive |
| **Non-disjoint** | Expressive | Complex |
| **Static rows** | Fast | Less flexible |
| **Dynamic rows** | Flexible | Runtime cost |

### When NOT to Use Row Polymorphism

- **For simple records**: Regular records suffice
- **For performance**: May add overhead
- **For closed systems**: Regular ADTs simpler

### Complexity Considerations

- **Constraint solving**: Can be complex
- **Type inference**: Undecidable in full
- **Label scoping**: Must be careful

### Limitations

- **Complexity**: Hard to implement correctly
- **Error messages**: Row errors confusing
- **Performance**: Label lookup overhead
- **Extensibility**: Must plan for extension
- **Tooling**: IDE support limited
- **Interaction with subtyping**: Complex

## Research Tools & Artifacts

Real-world row polymorphism systems:

| Tool | Why It Matters |
|------|----------------|
| **OCaml records** | Records in OCaml |
| **PureScript** | Row types in practice |
| **Koka** | Effect rows |
| **Haskell** | DuplicateRecordFields |

### Key Systems

- **PureScript**: Row types
- **Dhall**: Configuration language

## Research Frontiers

Current row polymorphism research:

| Direction | Key Papers | Challenge |
|-----------|------------|-----------|
| **Disjoint** | "Disjoint Rows" | Simplicity |
| **Overlap** | "Rows with Overlap" | Complexity |

### Hot Topics

1. **Rows in Rust**: Rust records
2. **Rows in TypeScript**: TypeScript types

## Implementation Pitfalls

Common row polymorphism bugs:

| Pitfall | Real Example | Prevention |
|---------|--------------|------------|
| **Overlap** | Label conflicts | Detect |
| **Order** | Row order | Normalize |
