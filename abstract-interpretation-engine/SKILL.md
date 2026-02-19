---
name: abstract-interpretation-engine
description: 'Implements abstract interpretation for static analysis. Use when: (1)
  Building static analyzers, (2) Program verification, (3) Static analysis.'
version: 1.0.0
tags:
- static-analysis
- abstract-interpretation
- fixpoint
- verification
difficulty: advanced
languages:
- python
- ocaml
dependencies:
- dataflow-analysis-framework

# Actionable triggers
triggers:
  - "implement abstract interpretation"
  - "build a static analyzer"
  - "compute program invariants"
  - "analyze variable ranges"
  - "detect null pointer dereferences"

# Ready-to-use prompts
action_prompts:
  - "Implement sign abstract domain (-, 0, +) for static analysis with lattice structure and comparisons"
  - "Build interval analysis for integer variables with widening operator"
  - "Implement nullness analysis to detect potential null dereferences"
  - "Create an abstract interpretation framework with lattice, transfer functions, and fixpoint computation"

# Optional slash commands
commands: []

# Script for direct execution
script: examples/abstract_interpreter.py
---

# Abstract Interpretation Engine

> **Status**: Ready to use | **Auto-trigger**: Yes | **Script**: `python examples/abstract_interpreter.py`

## Triggers

This skill activates when user mentions:
- Implementing abstract interpretation
- Building static analyzers
- Computing program invariants
- Bug detection via static analysis

## Action Prompts

Use these prompts directly:

```
Implement sign abstract domain with:
- Lattice: Bot < {-} < {-, 0} < {-, 0, +} < {0, +} < + < Top
- Join, meet, less-than operations
- Transfer functions for +, -, *, /
```

```
Build interval analysis:
- Interval domain [l, u] for integers
- Widening operator to ensure termination
- Transfer functions for arithmetic operations
- Handle loop widening thresholds
```

```
Implement nullness analysis:
- Lattice: Bottom < MaybeNull < NotNull < Top
- Track nullable variables through assignments
- Handle conditionals and branches
```

## When to Use

- Static program analysis
- Bug detection
- Program verification
- Type inference

## What This Skill Does

1. **Defines abstract domains** - Over-approximations
2. **Implements transfer** - Abstract semantics
3. **Computes fixpoints** - Chaotic iteration
4. **Handles widening** - Ensures termination

## Test Cases

| Program | Abstract State | Description |
|---------|---------------|-------------|
| `x := 5; y := x + 1` | x ∈ [5,5], y ∈ [6,6] | Constant propagation |
| `while x > 0: x := x - 1` | x ∈ [0, ∞) after loop | Widening at loop head |
| `if x > 0: y := 1 else: y := 0` | y ∈ {0, 1} | Join at branch merge |

### Using the Script

```bash
cd abstract-interpretation-engine
python examples/abstract_interpreter.py --domain sign --program "x := 5; y := x + 1"
python examples/abstract_interpreter.py --domain interval --file program.cfg
```

## Core Theory

```
Concrete domain:     C ⊆ P(Σ)
Abstract domain:     A with α: C → A, γ: A → C

Soundness:           c ⊆ γ(α(c))
Galois connection:   ∀c∈C, a∈A. α(c) ⊑ a ⇔ c ⊆ γ(a)
```

## Implementation

```python
from dataclasses import dataclass, field
from typing import Dict, List, Set, Callable, Generic, TypeVar, Optional
from abc import ABC, abstractmethod

# Abstract domain
class AbstractValue(ABC):
    """Abstract value"""
    
    @abstractmethod
    def lub(self, other: 'AbstractValue') -> 'AbstractValue':
        """Least upper bound"""
        pass
    
    @abstractmethod
    def glb(self, other: 'AbstractValue') -> 'AbstractValue':
        """Greatest lower bound"""
        pass
    
    @abstractmethod
    def less_or_equal(self, other: 'AbstractValue') -> bool:
        """Partial order ≤"""
        pass

# Interval domain
@dataclass
class Interval(AbstractValue):
    """Interval [lo, hi]"""
    lo: Optional[int]
    hi: Optional[int]
    
    def __post_init__(self):
        # Handle infinity
        if self.lo is None:
            self.lo = float('-inf')
        if self.hi is None:
            self.hi = float('inf')
    
    def lub(self, other: AbstractValue) -> 'AbstractValue':
        if not isinstance(other, Interval):
            return Top()
        return Interval(
            min(self.lo, other.lo),
            max(self.hi, other.hi)
        )
    
    def glb(self, other: AbstractValue) -> 'AbstractValue':
        if not isinstance(other, Interval):
            return Bottom()
        return Interval(
            max(self.lo, other.lo),
            min(self.hi, other.hi)
        )
    
    def less_or_equal(self, other: AbstractValue) -> bool:
        if not isinstance(other, Interval):
            return False
        return self.lo >= other.lo and self.hi <= other.hi
    
    def __repr__(self):
        return f"[{self.lo}, {self.hi}]"

@dataclass
class Top(AbstractValue):
    """Top element (unknown)"""
    
    def lub(self, other: AbstractValue) -> AbstractValue:
        return self
    
    def glb(self, other: AbstractValue) -> AbstractValue:
        return other
    
    def less_or_equal(self, other: AbstractValue) -> bool:
        return isinstance(other, Top)

@dataclass
class Bottom(AbstractValue):
    """Bottom element (unreachable)"""
    
    def lub(self, other: AbstractValue) -> AbstractValue:
        return other
    
    def glb(self, other: AbstractValue) -> AbstractValue:
        return self
    
    def less_or_equal(self, other: AbstractValue) -> bool:
        return True

# Sign domain
class Sign(AbstractValue):
    """Sign abstract domain: -, 0, +"""
    
    NEG = "negative"
    ZERO = "zero"
    POS = "positive"
    UNKNOWN = "unknown"
    
    def __init__(self, sign: str):
        self.sign = sign
    
    def lub(self, other: AbstractValue) -> AbstractValue:
        if not isinstance(other, Sign):
            return Top()
        
        signs = {self.sign, other.sign}
        
        if UNKNOWN in signs:
            return Sign(UNKNOWN)
        
        if NEG in signs and POS in signs:
            return Sign(UNKNOWN)
        
        if NEG in signs or ZERO in signs:
            return Sign(NEG) if NEG in signs else Sign(ZERO)
        
        return Sign(POS)
    
    def glb(self, other: AbstractValue) -> AbstractValue:
        if not isinstance(other, Sign):
            return Bottom()
        
        if self.sign == other.sign:
            return self
        
        return Bottom()  # Inconsistent
    
    def less_or_equal(self, other: AbstractValue) -> bool:
        if isinstance(other, Top):
            return True
        if not isinstance(other, Sign):
            return False
        
        order = {Bottom(), Sign(NEG), Sign(ZERO), Sign(POS), Top()}
        return order.index(self) <= order.index(other)

# Abstract environment
class AbstractEnvironment(Dict[str, AbstractValue]):
    """Map variables to abstract values"""
    
    def __getitem__(self, key: str) -> AbstractValue:
        return super().__getitem__(key)
    
    def lub(self, other: 'AbstractEnvironment') -> 'AbstractEnvironment':
        result = AbstractEnvironment()
        all_keys = set(self.keys()) | set(other.keys())
        
        for k in all_keys:
            v1 = self.get(k, Bottom())
            v2 = other.get(k, Bottom())
            result[k] = v1.lub(v2)
        
        return result

# Abstract semantics
class AbstractInterpreter:
    """Abstract interpreter"""
    
    def __init__(self, domain: AbstractValue):
        self.domain = domain
        self.cfg: Dict[str, 'Stmt'] = {}
        self.env: AbstractEnvironment = {}
    
    def interpret(self, program: 'Program') -> Dict[str, AbstractEnvironment]:
        """
        Interpret program abstractly
        
        Returns: map from node to abstract state
        """
        
        states = {}
        
        # Worklist for fixpoint
        worklist = list(program.cfg.keys())
        visited = set()
        
        # Initialize entry
        entry = program.entry
        states[entry] = AbstractEnvironment()
        
        while worklist:
            node = worklist.pop(0)
            
            if node not in states:
                states[node] = AbstractEnvironment()
            
            # Get predecessor states
            preds = program.cfg.predecessors(node)
            
            if preds:
                # Join states
                new_state = states[preds[0]].copy()
                for pred in preds[1:]:
                    new_state = new_state.lub(states[pred])
            else:
                new_state = AbstractEnvironment()
            
            # Apply transfer
            stmt = self.cfg.get(node)
            if stmt:
                new_state = self.transfer(stmt, new_state)
            
            # Check if changed
            if node not in visited or new_state != states[node]:
                states[node] = new_state
                visited.add(node)
                
                # Add successors
                for succ in program.cfg.successors(node):
                    if succ not in worklist:
                        worklist.append(succ)
        
        return states
    
    def transfer(self, stmt: 'Stmt', env: AbstractEnvironment) -> AbstractEnvironment:
        """Apply abstract transfer function"""
        
        result = AbstractEnvironment(env)
        
        match stmt:
            case Assign(x, expr):
                result[x] = self.eval_expr(expr, env)
            
            case If(cond, then, else_):
                # Both branches
                then_env = self.transfer_block(then, env)
                else_env = self.transfer_block(else_, env)
                return then_env.lub(else_env)
            
            case While(cond, body):
                # Will be handled by fixpoint
                pass
        
        return result
    
    def eval_expr(self, expr: 'Expr', env: AbstractEnvironment) -> AbstractValue:
        """Evaluate expression abstractly"""
        
        match expr:
            case Const(n):
                return Interval(n, n)
            
            case Var(x):
                return env.get(x, Bottom())
            
            case BinOp(op, e1, e2):
                v1 = self.eval_expr(e1, env)
                v2 = self.eval_expr(e2, env)
                
                return self.abstract_binop(op, v1, v2)
            
            case _:
                return Top()
    
    def abstract_binop(self, op: str, v1: AbstractValue, v2: AbstractValue) -> AbstractValue:
        """Abstract binary operation"""
        
        if isinstance(v1, Bottom) or isinstance(v2, Bottom):
            return Bottom()
        
        if isinstance(v1, Top) or isinstance(v2, Top):
            return Top()
        
        if isinstance(v1, Interval) and isinstance(v2, Interval):
            return self.interval_binop(op, v1, v2)
        
        return Top()
    
    def interval_binop(self, op: str, i1: Interval, i2: Interval) -> AbstractValue:
        """Interval arithmetic"""
        
        lo1, hi1 = i1.lo, i1.hi
        lo2, hi2 = i2.lo, i2.hi
        
        # Handle infinity
        if lo1 == float('-inf') or hi1 == float('inf'):
            return Top()
        if lo2 == float('-inf') or hi2 == float('inf'):
            return Top()
        
        if op == '+':
            return Interval(lo1 + lo2, hi1 + hi2)
        elif op == '-':
            return Interval(lo1 - hi2, hi1 - lo2)
        elif op == '*':
            products = [lo1*lo2, lo1*hi2, hi1*lo2, hi1*hi2]
            return Interval(min(products), max(products))
        
        return Top()

# Widening
class Widening:
    """Widening operator for termination"""
    
    @staticmethod
    def widen_interval(i1: Interval, i2: Interval) -> Interval:
        """Widen intervals"""
        
        lo = i1.lo if i2.lo >= i1.lo else float('-inf')
        hi = i1.hi if i2.hi <= i1.hi else float('inf')
        
        return Interval(lo, hi)
    
    @staticmethod
    def widen_sign(s1: Sign, s2: Sign) -> AbstractValue:
        """Widen signs"""
        
        # If both known and equal, keep
        if s1.sign == s2.sign:
            return s1
        
        return Top()
```

## Abstract Domains

| Domain | Elements | Operations |
|--------|----------|------------|
| **Sign** | -, 0, + | lub, glb |
| **Interval** | [l, u] | +, -, * |
| **Polyhedra** | Linear constraints | Intersection |
| **Relational** | Numeric relations | Join, meet |
| **Pointer** | Points-to sets | Aliasing |

## Widening

```python
def widening_fixpoint(transition, initial, widening, max_iterations=1000):
    """Compute fixpoint with widening"""
    
    prev = initial
    curr = initial
    
    for i in range(max_iterations):
        curr = transition(prev)
        
        # Apply widening
        curr = widening(prev, curr)
        
        if curr.less_or_equal(prev):
            return curr
        
        prev = curr
    
    return curr  # May not have converged
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| **Galois connection** | α ↔ γ between concrete/abstract |
| **Soundness** | Over-approximation |
| **Widening** | Force termination |
| **Fixpoint** | Stable state |

## Tips

- Choose appropriate abstract domain
- Apply widening for loops
- Balance precision vs speed
- Verify soundness

## Related Skills

- `dataflow-analysis-framework` - Dataflow
- `invariant-generator` - Invariants
- `symbolic-execution-engine` - Symbolic execution

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| **Cousot & Cousot, "Abstract Interpretation" (POPL 1977)** | Foundational paper establishing the framework |
| **Cousot, "Theoretical Basis for Abstract Interpretation"** | Mathematical foundations |
| **Nielson, Nielson & Hankin, "Principles of Program Analysis"** | Comprehensive textbook on static analysis |
| **Graf & Saidi, "Construction of Abstract State Graphs"** | Predicate abstraction |
| **Blazy, Leroy, et al., "Formal Verification of a C Value Analysis Based on Abstract Interpretation" (SAS 2013)** | Verified abstract interpreter in Coq |

## Tradeoffs and Limitations

### Domain Tradeoffs

| Domain | Precision | Cost | Example Use |
|--------|-----------|------|-------------|
| **Sign** | Low | O(1) | Division by zero detection |
| **Interval** | Medium | O(1) | Array bounds |
| **Polyhedra** | High | Expensive | Relational invariants |
| **Octagon** | Medium-High | Moderate | Numerical analysis |

### When NOT to Use Abstract Interpretation

- **For decidable analysis**: Consider model checking for finite-state
- **For path-sensitive analysis**: Consider symbolic execution
- **For interprocedural**: Requires call-string or analysis summary techniques

### Complexity Analysis

- **Time complexity**: Typically O(f × n) where f = transfer function complexity, n = program size
- **Space complexity**: O(d × n) where d = size of abstract domain × number of program points
- **Widening**: Guarantees termination but may lose precision
- **Worklist algorithms**: Often converge faster than naive iteration

### Limitations

- **Imprecision**: By design (over-approximation); may produce false positives
- **Domain choice critical**: Wrong domain = useless analysis
- **Interprocedural analysis**: Significantly more complex
- **Soundness burden**: Must analyze ALL paths; partial analysis is unsound

## Assessment Criteria

A high-quality abstract interpreter should have:

| Criterion | What to Look For |
|-----------|------------------|
| **Soundness** | Never misses a real bug (no false negatives) |
| **Precision** | Few false positives |
| **Termination** | Uses widening correctly |
| **Efficiency** | Scales to large programs |
| **Domain** | Appropriate for target properties |
| **Modularity** | Easy to add new domains |

### Quality Indicators

✅ **Good**: Sound, terminates, appropriate precision for domain
⚠️ **Warning**: Unsound in edge cases, imprecise domain
❌ **Bad**: Misses real bugs (unsound), doesn't terminate

## Research Tools & Artifacts

Industrial-strength abstract interpreters:

| Tool | Organization | What to Learn |
|------|--------------|---------------|
| **Astrée** | AbsInt | Industrial C static analysis |
| **Facebook Infer** | Facebook/Meta | Compositional separation logic |
| **Frama-C** | CEA/Inria | C verification platform |
| **Polyspace** | MathWorks | Industrial static analysis |
| **Clang Static Analyzer** | LLVM | Source-level analysis |
| **PA research tools** | Various | Academic prototypes |

### Academic Tools

- **APRON** - Numerical abstract domains library
- **ELINA** - Machine learning for numerical analysis
- **PHA** - Polyhedral analyzer
- **Juliet** (NIST) - Test suite for static analyzers

## Research Frontiers

### 1. Abstract Domains
- **Goal**: More precise over-approximation
- **Current**: Polyhedra, octagons, zones, congruences
- **Research**: Template polyhedra (Sankaranarayanan et al.), reduced product
- **Challenge**: Precision vs. performance

### 2. Abstract Interpretation for Probabilistic Programs
- **Goal**: Analyze programs with randomness
- **Techniques**: Probabilistic relational reasoning, distribution semantics
- **Papers**: "Abstract Interpretation of Probabilistic Programs" (Minks)
- **Applications**: Machine learning verification, security

### 3. Non-Termination Analysis
- **Goal**: Prove programs don't loop forever
- **Techniques**: Ranking functions, loop summarization
- **Papers**: "Proving Non-Termination" (Gupta et al.)
- **Tool**: AProVE (termination prover)

### 4. Concolic Execution
- **Goal**: Combine concrete and symbolic execution
- **Techniques**: Path merging, symbolic simplification
- **Papers**: "DART: Directed Automated Random Testing" (Godefroid et al.)
- **Tools**: KLEE, Manticore, S2E

## Implementation Pitfalls

| Pitfall | Real Consequence | Solution |
|---------|-----------------|----------|
| **Unsoundness** | Missing real bugs | Trace all paths, always join |
| **Non-termination** | Analysis hangs | Widening at every loop |
| **Imprecision** | Too many false positives | Choose better domain |
| **Path explosion** | Exponential blowup | Summarization, incremental |
| **Heap modeling** | Pointer analysis bugs | Choose alias domain carefully |

### The "Widening is Subtle" Problem

Widening must be applied correctly or lose precision:

```python
# Naive widening - loses precision
def widen(i1, i2):
    if i2.lo < i1.lo: lo = -inf
    if i2.hi > i1.hi: hi = +inf
    return Interval(lo, hi)

# Better - only widen when growing
def widen(i1, i2):
    lo = i1.lo if i2.lo >= i1.lo else float('-inf')
    hi = i1.hi if i2.hi <= i1.hi else float('inf')
    return Interval(lo, hi)
```

### The "Path Sensitivity" Tradeoff

More precise but expensive:

```python
# Path-insensitive (cheaper)
if x > 0: y = x  # y: [1, +inf]
else: y = -x     # y: [1, +inf]
# Join: y: [1, +inf]

# Path-sensitive (expensive)  
if x > 0: y = x  # Then-branch: y: [1, +inf]
else: y = -x     # Else-branch: y: [1, +inf]
# Keep separate states!
```
