---
name: dataflow-analysis-framework
description: 'Implements general dataflow analysis framework. Use when: (1) Building
  compilers, (2) Static analysis tools, (3) Program verification.'
version: 1.0.0
tags:
- static-analysis
- dataflow
- lattice
- analysis
difficulty: intermediate
languages:
- python
- ocaml
dependencies: []
---

# Dataflow Analysis Framework

Implements generalized dataflow analysis for static program analysis.

## When to Use

- Building static analyzers
- Compiler optimizations
- Bug detection
- Program understanding

## What This Skill Does

1. **Defines lattices** - Complete partial orders
2. **Implements frameworks** - Forward/backward, may/must
3. **Solves equations** - Worklist, iterative solving
4. **Handles complexity** - Intra/interprocedural

## Framework Components

```
Dataflow Framework:
  - Direction: Forward or Backward
  - Lattice: Values and operations
  - Transfer: Statement → Lattice
  - Meet: Lattice meet operation
  - Boundary: Entry/exit conditions
```

## Implementation

```python
from dataclasses import dataclass, field
from typing import Dict, List, Set, Callable, Generic, TypeVar, Optional
from abc import ABC, abstractmethod
from enum import Enum

T = TypeVar('T')

# Lattice definition
class Lattice(ABC, Generic[T]):
    """Abstract lattice"""
    
    @abstractmethod
    def top(self) -> T:
        """Top element"""
        pass
    
    @abstractmethod
    def bottom(self) -> T:
        """Bottom element"""
        pass
    
    @abstractmethod
    def meet(self, a: T, b: T) -> T:
        """Meet (greatest lower bound)"""
        pass
    
    @abstractmethod
    def join(self, a: T, b: T) -> T:
        """Join (least upper bound)"""
        pass
    
    @abstractmethod
    def less_than(self, a: T, b: T) -> bool:
        """Partial order (≤)"""
        pass

# Direction
class Direction(Enum):
    FORWARD = "forward"
    BACKWARD = "backward"

# Dataflow problem
@dataclass
class DataflowProblem(Generic[T]):
    """Dataflow problem specification"""
    
    direction: Direction
    lattice: Lattice[T]
    transfer: Dict[str, Callable[[T, 'Stmt'], T]]
    boundary: T
    init: T
    
    # For control flow
    cfg: 'ControlFlowGraph'
    statements: List['Stmt']

class WorklistSolver(Generic[T]):
    """Worklist algorithm for dataflow"""
    
    def __init__(self, problem: DataflowProblem[T]):
        self.problem = problem
        self.in_values: Dict[str, T] = {}
        self.out_values: Dict[str, T] = {}
        self.worklist: Set[str] = set()
    
    def solve(self) -> Dict[str, T]:
        """Solve dataflow equations"""
        
        # Initialize
        for stmt_id in self.problem.cfg.nodes:
            self.in_values[stmt_id] = self.problem.bottom
            self.out_values[stmt_id] = self.problem.bottom
        
        # Add all nodes to worklist
        self.worklist = set(self.problem.cfg.nodes)
        
        # Initialize boundary
        entry = self.problem.cfg.entry
        if self.problem.direction == Direction.FORWARD:
            self.out_values[entry] = self.problem.boundary
        else:
            self.in_values[entry] = self.problem.boundary
        
        # Worklist algorithm
        while self.worklist:
            node = self.worklist.pop()
            
            # Compute IN
            if self.problem.direction == Direction.FORWARD:
                in_val = self.compute_forward_in(node)
            else:
                in_val = self.compute_backward_in(node)
            
            # Check if changed
            if in_val == self.in_values[node]:
                continue
            
            self.in_values[node] = in_val
            
            # Transfer function
            out_val = self.transfer(node, in_val)
            
            if out_val != self.out_values[node]:
                self.out_values[node] = out_val
                # Add successors to worklist
                for succ in self.problem.cfg.successors(node):
                    self.worklist.add(succ)
        
        return self.in_values if self.problem.direction == Direction.FORWARD else self.out_values
    
    def compute_forward_in(self, node: str) -> T:
        """Compute IN for forward analysis"""
        
        preds = self.problem.cfg.predecessors(node)
        
        if not preds:
            return self.problem.boundary
        
        result = self.out_values[preds[0]]
        for pred in preds[1:]:
            result = self.problem.lattice.meet(result, self.out_values[pred])
        
        return result
    
    def compute_backward_in(self, node: str) -> T:
        """Compute IN for backward analysis"""
        
        succs = self.problem.cfg.successors(node)
        
        if not succs:
            return self.problem.boundary
        
        result = self.in_values[succs[0]]
        for succ in succs[1:]:
            result = self.problem.lattice.meet(result, self.in_values[succ])
        
        return result
    
    def transfer(self, node: str, in_val: T) -> T:
        """Apply transfer function"""
        
        if node in self.problem.transfer:
            return self.problem.transfer[node](in_val, self.problem.cfg.stmt(node))
        
        return in_val

# Example: Constant Propagation Lattice
class ConstantPropagationLattice(Lattice[int]):
    """Constant propagation lattice"""
    
    def top(self) -> int:
        return float('inf')  # NAC - Not A Constant
    
    def bottom(self) -> int:
        return float('-inf')  # Undefined
    
    def meet(self, a: int, b: int) -> int:
        if a == b:
            return a
        return float('inf')  # NAC
    
    def join(self, a: int, b: int) -> int:
        if a == b:
            return a
        return float('inf')
    
    def less_than(self, a: int, b: int) -> bool:
        # Simplified
        return a == b

# Example: Available Expressions
class AvailableExpressionsLattice(Lattice[Set[tuple]]):
    """Available expressions lattice"""
    
    def top(self) -> Set[tuple]:
        return set()  # Empty = most precise
    
    def bottom(self) -> Set[tuple]:
        return set()  # Universal set in practice
    
    def meet(self, a: Set[tuple], b: Set[tuple]) -> Set[tuple]:
        return a & b  # Intersection
    
    def join(self, a: Set[tuple], b: Set[tuple]) -> Set[tuple]:
        return a | b  # Union
    
    def less_than(self, a: Set[tuple], b: Set[tuple]) -> bool:
        return a.issubset(b)

# Live Variable Analysis
class LiveVariableAnalysis:
    """Live variable analysis"""
    
    def __init__(self, cfg):
        self.cfg = cfg
        self.problem = DataflowProblem(
            direction=Direction.BACKWARD,
            lattice=SetLattice(),
            transfer={},
            boundary=set(),
            init=set(),
            cfg=cfg
        )
    
    def analyze(self) -> Dict[str, Set[str]]:
        """Analyze live variables"""
        
        def transfer(stmt_id: str, stmt: 'Stmt', out_val: Set[str]) -> Set[str]:
            in_val = set(out_val)
            
            match stmt:
                case Assign(x, e):
                    in_val.discard(x)  # x is overwritten
                    in_val |= vars(e)  # x used in e
                case If(cond, _, _):
                    in_val |= vars(cond)
                case _:
                    pass
            
            return in_val
        
        self.problem.transfer = transfer
        solver = WorklistSolver(self.problem)
        return solver.solve()

class SetLattice(Lattice[Set]):
    """Lattice of sets"""
    
    def top(self) -> Set:
        return set()  # Empty set = top (all dead)
    
    def bottom(self) -> Set:
        return set()  # Universe in practice
    
    def meet(self, a: Set, b: Set) -> Set:
        return a & b
    
    def join(self, a: Set, b: Set) -> Set:
        return a | b
    
    def less_than(self, a: Set, b: Set) -> bool:
        return a.issubset(b)
```

## Analysis Types

| Analysis | Direction | Lattice | Meet |
|----------|----------|---------|------|
| **Reaching definitions** | Forward | Sets | Union |
| **Available expressions** | Forward | Sets | Intersection |
| **Live variables** | Backward | Sets | Union |
| **Very busy expressions** | Backward | Sets | Intersection |
| **Constant propagation** | Forward | Constants | Meet |

## Key Concepts

| Concept | Description |
|---------|-------------|
| **Lattice** | Partial order with lub/glb |
| **Transfer function** | Statement transformation |
| **Worklist** | Efficient solving |
| **MOP** | Meet-over-all-paths solution |
| **MFP** | Maximum fixed point |

## Tips

- Choose correct direction
- Define lattice carefully
- Handle cycles with care
- Consider speed vs precision

## Related Skills

- `constant-propagation-pass` - Constant analysis
- `invariant-generator` - Loop invariants
- `abstract-interpretation-engine` - Abstract interpretation

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| **Aho et al., "Compilers: Principles, Techniques, and Tools" (1986)** | Dragon Book; chapters on dataflow |
| **Kam & Ullman, "Monotone Data Flow Analysis Frameworks" (1977)** | Foundational dataflow theory |
| **Cousot & Cousot, "Abstract Interpretation" (POPL 1977)** | General framework |
| **Marlowe & Ryder, "Data Flow Analysis" (1990)** | Practical frameworks |
| **Reps, "Program Analysis via Graph Reachability" (1998)** | IFDS/IDE frameworks |

## Tradeoffs and Limitations

### Analysis Approach Tradeoffs

| Approach | Pros | Cons |
|----------|------|------|
| **May analysis** | Scalable | Imprecise |
| **Must analysis** | Precise | Limited |
| **Bitvector** | Efficient | Domain-specific |
| **IFDS/IDE** | Interprocedural | Complex |

### When NOT to Use Dataflow Analysis

- **For precise aliasing**: Use pointer analysis instead
- **For concurrent programs**: Model checking or abstract interpretation
- **For complex properties**: Consider symbolic execution

### Complexity Considerations

- **Time**: O(n × d) where n = program size, d = domain size
- **Space**: O(n) for worklist, O(n × d) for lattice values
- **Convergence**: Lattice height × number of nodes iterations worst case

### Limitations

- **Imprecision**: Must alias, may alias in pointer analysis
- **Interprocedural**: Requires call graphs and summary techniques
- **Context sensitivity**: Increases complexity exponentially
- **Scalability**: Large programs challenge framework
- **Soundness**: Must track all paths; partial is unsound
- **Non-monotonic**: Some analyses not monotone (e.g., side effects)

## Research Tools & Artifacts

Dataflow analysis tools:

| Tool | Application | What to Learn |
|------|-------------|---------------|
| **Soot** | Java | Whole-program analysis |
| **WALA** | Java/IBM | Static analysis framework |
| **LLVM analysis passes** | C/C++ | Compiler-integrated |
| **Infer** | Facebook | Industrial static analysis |
| **CodeQL** | GitHub | Query-based analysis |

### Frameworks

- **IFDS** (Interprocedural Finite Distributive Subsets) - Context-sensitive
- **IDE** (Interprocedural Distributive Environment) - General IFDS
- **Datalog** - Declarative analysis

## Research Frontiers

### 1. Demand-Driven Analysis
- **Goal**: Compute only needed information
- **Approach**: Reverse dataflow, query-based
- **Papers**: "Demand-Driven Dataflow Analysis"

### 2. Probabilistic Analysis
- **Goal**: Estimate likelihood of properties
- **Approach**: Probabilistic program analysis
- **Papers**: "Probabilistic Dataflow Analysis"

## Implementation Pitfalls

| Pitfall | Real Consequence | Solution |
|---------|-----------------|----------|
| **Wrong direction** | Analysis doesn't converge | Forward vs backward |
| **Non-monotonic** | Unsound results | Use abstract interpretation |
| **Missing aliases** | Imprecision | Pointer analysis first |
