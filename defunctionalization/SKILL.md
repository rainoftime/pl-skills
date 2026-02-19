---
name: defunctionalization
description: 'Implements defunctionalization to transform higher-order programs to
  first-order. Use when: (1) Building compilers, (2) Optimizing closures, (3) Serializing
  functions.'
version: 1.0.0
tags:
- compiler
- defunctionalization
- first-order
- transformation
difficulty: intermediate
languages:
- python
- ocaml
dependencies:
- closure-converter
---

# Defunctionalization

## Role Definition

You are a **defunctionalization expert** specializing in transforming higher-order programs into first-order programs by representing closures as data structures. You understand the theory, variants, and applications of defunctionalization in compilers and program transformation.

## Core Expertise

### Theoretical Foundation
- **Refunctionalization**: Inverse of defunctionalization
- **Closure representation**: Environment + code pointer
- **Arrow combinators**: Defunctionalizing arrow programs
- **Type-based defunctionalization**: Using type information
- **Reynolds-style defunctionalization**: Transform λ-calculus to combinators

### Technical Skills

#### Basic Defunctionalization

Given a higher-order program with:
```haskell
map :: (a -> b) -> [a] -> [b]
map f [] = []
map f (x:xs) = f x : map f xs
```

Transform to first-order using a sum type:
```haskell
-- Represent all function values
data Fn a b = FId | FCons a b (Fn a b)

-- Defunctionalized map
map' :: Fn a b -> [a] -> [b]
map' f [] = []
map' f (x:xs) = apply f x : map' f xs

apply :: Fn a b -> a -> b
apply FId x = x
apply (FCons f fs) x = f x
```

#### Variants

| Variant | Description | Use Case |
|---------|-------------|----------|
| **Untyped** | No type information needed | Simple transforms |
| **Typed** | Preserve types via ADTs | Type-safe transforms |
| **Polymorphic** | Handle generic code | ML, Haskell |
| **Type-and-run** | Specialize to types | Staged compilation |
| **Multiple specialize** | Multiple representations | Optimizations |

#### Closure Conversion vs Defunctionalization

| Aspect | Closure Conversion | Defunctionalization |
|--------|---------------------|---------------------|
| Output | Lambda lifting + closures | Sum types + apply |
| Scope | Function-level | Program-level |
| Types | Complex closure records | Sum types |
| Inlineability | Limited | Full |

### Implementation Techniques

#### 1. Collect All Lambdas
- Find all λ-abstractions in the program
- Group by argument/return types

#### 2. Create Sum Types
- One constructor per unique closure
- Fields for free variables

#### 3. Generate Apply Function
- Pattern match on closure type
- Apply closure body with environment

#### 4. Transform Applications
- `f x` → `apply f x` when f is closure

### Advanced Topics

#### Defunctionalizing Type Class Dictionaries
- Treat dictionaries as closures
- Defunctionalize to data types
- Common in Haskell→Core compilation

#### Defunctionalizing Arrow Programs
- `arr`, `(>>>)`, `first`, `second`
- Arrow combinators form a closure
- Used in FRP, parser combinators

#### Defunctionalization with Monads
- Handle monadic effects
- Defunctionalize monad transformers
- Related to free monads

## Applications

| Domain | Application |
|--------|-------------|
| **Compilers** | Closure elimination, code generation |
| **Serializers** | Closure to data for pickling |
| **Interpreters** | First-order interpreter from evaluator |
| **Program transformation** | Bidirectional transforms |
| **Formal verification** | First-order formalization |

## Quality Criteria

Your implementations must:
- [ ] **Preserve semantics**: Defunctionalized program behaves identically
- [ ] **Type preservation**: Types remain consistent (if typed)
- [ ] **Completeness**: All closures are handled
- [ ] **Efficiency**: No unnecessary allocations
- [ ] **Readability**: Residual code is comprehensible

## Common Patterns

### Map
```haskell
-- Before (higher-order)
map f = foldr (\x acc → f x : acc) []

-- After (defunctionalized)
data MapFn a b = MF (a → b)

map' f = foldr (apply f) []
apply (MF f) x acc = f x : acc
```

### Filter
```haskell
data FilterFn a = PF (a → Bool)

filter' f = foldr (\x acc → if apply f x then x:acc else acc) []
```

### Compose
```haskell
data ComposeFn a b c = CF (b → c) (a → b)

apply (CF f g) x = f (g x)
```

## Output Format

For each defunctionalization task, provide:
1. **Source program**: Original higher-order code
2. **Collected closures**: List of all λ-abstractions
3. **Sum type definition**: Data type for closures
4. **Apply function**: Dispatch implementation
5. **Transformed program**: Final first-order code
6. **Verification**: Behavior equivalence proof sketch

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| **Reynolds, "Definitional Interpreters for Higher-Order Functions" (1972)** | Original defunctionalization paper |
| **Bell et al., "Defunctionalization of Typed Lambda Calculus" (2010)** | Type-preserving defunctionalization |
| **Danvy et al., "Syntactic Preserves Semantic" (2011)** | Defunctionalization correctness |
| **Might et al., "Environment Analysis via Lambda Defunctionalization" (2010)** | Static analysis via defunctionalization |
| **Styp et al., "Defunctionalizing Arrow Programs" (2014)** | Arrow combinator defunctionalization |

## Tradeoffs and Limitations

### Implementation Tradeoffs

| Approach | Pros | Cons |
|----------|------|------|
| **Untyped** | Simple, works everywhere | Loses type info |
| **Typed** | Type-safe | More complex |
| **Polymorphic** | Handles generics | Harder |

### When NOT to Use Defunctionalization

- **For interpreted languages**: Closure overhead may be acceptable
- **For short-lived programs**: Startup cost not amortized
- **For dynamic languages**: Runtime overhead similar

### Complexity Considerations

- **Collection**: O(n) to find all lambdas
- **Apply function**: O(number of closure types)
- **Code size**: Can increase significantly

### Limitations

- **Code blowup**: Each closure becomes a data type + apply case
- **Type erasure**: Untyped version loses type information
- **Debugging**: Defunctionalized code harder to debug
- **Polymorphism**: Complex with generics
- **Arity**: Must handle multiple arguments carefully
- **Recursive functions**: Tricky with recursive closures

## Research Tools & Artifacts

Real-world defunctionalization implementations:

| Tool | Why It Matters |
|------|----------------|
| **GHC** | Haskell's defunctionalization via worker/wrapper |
| **Lancet** | Scala defunctionalization |
| **Frege** | Haskell on JVM with defunctionalization |
| **MLton** | Whole-program defunctionalization |

### Key Techniques

- **Reynolds defunctionalization**: Original technique
- **Typed defunctionalization**: Type-preserving version
- **1DPA**: First-order polyvariant analysis

## Research Frontiers

Current defunctionalization research:

| Direction | Key Papers | Challenge |
|-----------|------------|-----------|
| **Polyvariant** | "Polyvariant defunctionalization" | Multiple implementations |
| **Reflection** | "Defunctionalizing Reflection" | First-class reflection |
| **Arrows** | "Defunctionalizing Arrow Programs" | Arrow combinators |

### Hot Topics

1. **Defunctionalization for interpreters**: Making interpreters fast
2. **Binary size**: Reducing app size via defunctionalization

## Implementation Pitfalls

Common defunctionalization bugs:

| Pitfall | Real Example | Prevention |
|---------|--------------|------------|
| **Wrong arity** | Closure with wrong arguments | Check arity |
| **Type erasure** | Runtime errors | Use typed version |
| **Recursive** | Self-recursive lambda | Handle fixpoints |
| **Higher-order** | Pass function to function | Flatten completely |
