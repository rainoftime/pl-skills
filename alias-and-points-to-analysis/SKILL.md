---
name: alias-and-points-to-analysis
description: "Implements alias and points-to analysis for pointer programs. Use for: (1) Optimizing compilers, (2) Verifying memory safety, (3) Program understanding, (4) Parallelization."
version: 1.0.0
tags:
- static-analysis
- alias-analysis
- points-to-analysis
- pointers
- optimization
difficulty: intermediate
languages:
- python
- c++
- rust
dependencies:
- dataflow-analysis-framework
---

# Alias and Points-To Analysis

Implements interprocedural alias and points-to analysis for pointer programs.

## When to Use

- Compiler optimization
- Memory safety verification
- Program understanding
- Security analysis
- Parallelization
- Bug detection

## What This Skill Does

1. **Points-to analysis** - Compute pointer targets
2. **Alias detection** - Find aliased locations
3. **Interprocedural** - Across function calls
4. **Flow-sensitive** - With control flow

## Analysis Types

| Type | Precision | Speed |
|------|-----------|-------|
| **Must-alias** | Definitely aliased | Fast |
| **May-alias** | Possibly aliased | Medium |
| **No-alias** | Definitely not aliased | Medium |

## Key Concepts

| Concept | Description |
|---------|-------------|
| **Points-to** | Set of locations a pointer may reach |
| **Points-To Set** | Memory locations a pointer may reference |
| **Alias** | Two references may denote same location |
| **Must-alias** | Always aliased |
| **May-alias** | Possibly aliased |
| **Flow Sensitivity** | Different results at different program points |
| **Context Sensitivity** | Different results for different call contexts |
| **Allocation Site** | Abstract location representing all objects created there |
| **Inclusion-based** | Andersen's (subset constraints) |
| **Unification-based** | Steensgaard's (union-find) |

## Implementation

```python
from dataclasses import dataclass, field
from typing import Dict, Set, List, Optional, Tuple

@dataclass
class Location:
    """Memory location"""
    name: str
    offset: Optional[int] = None

@dataclass
class PointsToSet:
    """Set of locations a pointer may point to"""
    targets: Set[Location] = field(default_factory=set)

class AliasAnalysis:
    """Flow-insensitive alias analysis"""
    
    def __init__(self):
        self.pts: Dict[str, PointsToSet] = {}  # pointer -> points-to set
        self.globals: Set[str] = set()
        self.heap: Set[str] = set()
    
    def analyze(self, program: 'Program') -> Dict[Tuple[str, str], str]:
        """
        Compute alias relationships
        
        Returns: {(x, y): alias_type}
                 where alias_type in {MUST, MAY, NO}
        """
        
        # Build call graph
        self.call_graph = self.build_call_graph(program)
        
        # Initialize points-to
        self.initialize(program)
        
        # Iterative analysis
        changed = True
        while changed:
            changed = self.iterate(program)
        
        # Compute alias information
        return self.compute_aliases()
    
    def iterate(self, program: 'Program') -> bool:
        """Single iteration of analysis"""
        
        changed = False
        
        for func in program.functions:
            for stmt in func.body:
                changed |= self.analyze_stmt(stmt)
        
        # Interprocedural
        for call in program.calls:
            changed |= self.analyze_call(call)
        
        return changed
    
    def analyze_stmt(self, stmt: 'Stmt') -> bool:
        """Analyze single statement"""
        
        changed = False
        
        match stmt:
            case Assign(x, y):
                # x = y: copy points-to
                if y in self.pts:
                    old = self.pts.get(x, PointsToSet())
                    self.pts[x] = old
                    if old != self.pts.get(x):
                        changed = True
            
            case AddressOf(x, y):
                # x = &y: points to y
                self.pts[x] = PointsToSet({Location(y)})
                changed = True
            
            case Load(x, y):
                # x = *y: dereference
                if y in self.pts:
                    targets = self.pts[y].targets
                    new_pts = set()
                    for loc in targets:
                        if isinstance(loc, HeapLocation):
                            new_pts.add(loc)
                    if x not in self.pts or self.pts[x].targets != new_pts:
                        self.pts[x] = PointsToSet(new_pts)
                        changed = True
            
            case Store(x, y):
                # *x = y
                if x in self.pts:
                    # Points-to of y may be stored
                    pass
            
            case Alloc(x):
                # x = new T: heap allocation
                heap_loc = HeapLocation(f"heap_{len(self.heap)}")
                self.pts[x] = PointsToSet({heap_loc})
                self.heap.add(heap_loc.name)
                changed = True
        
        return changed
    
    def compute_aliases(self) -> Dict[Tuple[str, str], str]:
        """Compute alias pairs"""
        
        aliases = {}
        
        pointers = list(self.pts.keys())
        
        for i, p1 in enumerate(pointers):
            for p2 in pointers[i+1:]:
                alias_type = self.check_alias(p1, p2)
                if alias_type != "NO":
                    aliases[(p1, p2)] = alias_type
                    aliases[(p2, p1)] = alias_type
        
        return aliases
    
    def check_alias(self, x: str, y: str) -> str:
        """Check alias relationship"""
        
        pts_x = self.pts.get(x, PointsToSet()).targets
        pts_y = self.pts.get(y, PointsToSet()).targets
        
        if not pts_x or not pts_y:
            return "NO"
        
        # Must-alias: exactly same points-to
        if pts_x == pts_y and len(pts_x) == 1:
            return "MAY"
        
        # May-alias: intersection non-empty
        if pts_x & pts_y:
            return "MAY"
        
        return "NO"
```

## Andersen's Analysis

```python
class AndersensAnalysis(AliasAnalysis):
    """Andersen's inclusion-based analysis (O(n³))"""
    
    def analyze(self, program: 'Program') -> Dict:
        """Andersen-style analysis"""
        
        # Constraint generation
        constraints = self.generate_constraints(program)
        
        # Solve constraints iteratively
        return self.solve_constraints(constraints)
    
    def generate_constraints(self, program: 'Program') -> List:
        """Generate points-to constraints"""
        
        constraints = []
        
        for func in program.functions:
            for stmt in func.body:
                match stmt:
                    case Assign(x, y):
                        # x ⊆ pts(y)
                        constraints.append(('subset', x, y))
                    
                    case AddressOf(x, y):
                        # pts(x) ⊇ {y}
                        constraints.append(('points-to', x, y))
                    
                    case Load(x, y):
                        # For each p in pts(y): pts(x) ⊆ pts(p)
                        constraints.append(('load', x, y))
                    
                    case Store(x, y):
                        # For each p in pts(x): pts(p) ⊆ pts(y)
                        constraints.append(('store', x, y))
        
        return constraints
    
    def solve_constraints(self, constraints: List) -> Dict:
        """Solve constraints by fixed point"""
        
        # Initialize
        self.pts = {v: PointsToSet() for v in get_all_vars()}
        
        # Iterate until fixed point
        while True:
            old_pts = dict(self.pts)
            
            for constraint in constraints:
                self.apply_constraint(constraint)
            
            if self.pts == old_pts:
                break
        
        return self.compute_aliases()
    
    def apply_constraint(self, constraint):
        """Apply single constraint"""
        
        kind, x, y = constraint
        
        match kind:
            case 'subset':
                # pts(x) ⊆ pts(y)
                self.pts[y].targets |= self.pts[x].targets
            
            case 'points-to':
                # pts(x) ⊇ {y}
                self.pts[x].targets.add(Location(y))
            
            case 'load':
                # x = *y
                for loc in self.pts.get(y, PointsToSet()).targets:
                    self.pts[x].targets |= self.pts.get(loc.name, PointsToSet()).targets
            
            case 'store':
                # *x = y
                for loc in self.pts.get(x, PointsToSet()).targets:
                    self.pts[loc.name].targets |= self.pts.get(y, PointsToSet()).targets
```

## Steensgaard's Analysis

```python
class SteensgaardAnalysis(AliasAnalysis):
    """Steensgaard's unification-based analysis (almost linear)"""
    
    def analyze(self, program: 'Program') -> Dict:
        """Unification-based analysis"""
        
        # Union-find for locations
        self.parent = {}
        self.rank = {}
        
        # Initialize
        for v in get_all_vars():
            self.make_set(v)
        
        # Unification
        for func in program.functions:
            for stmt in func.body:
                self.unify_stmt(stmt)
        
        # Extract points-to from unions
        return self.extract_points_to()
    
    def make_set(self, x):
        self.parent[x] = x
        self.rank[x] = 0
    
    def find(self, x):
        if self.parent[x] != x:
            self.parent[x] = self.find(self.parent[x])
        return self.parent[x]
    
    def union(self, x, y):
        """Unify two locations"""
        
        px, py = self.find(x), self.find(y)
        
        if px == py:
            return
        
        if self.rank[px] < self.rank[py]:
            px, py = py, px
        
        self.parent[py] = px
        if self.rank[px] == self.rank[py]:
            self.rank[px] += 1
    
    def unify_stmt(self, stmt):
        """Unify based on statement"""
        
        match stmt:
            case Assign(x, y):
                self.union(x, y)
            
            case Load(x, y):
                # Unify x with all of y's targets
                pass
            
            case Store(x, y):
                pass
```

## Applications

- Dead store elimination
- Scalar replacement
- Lock elision
- Memory safety
- Parallelization (dependence analysis)
- Bug detection (null pointer, use-after-free)
- Security analysis (taint tracking)
- IDE features (find references)
- Garbage collector implementation

## Tips

- Start with Andersen's for precision, Steensgaard's for speed
- Use allocation-site abstraction for heap
- Add field sensitivity for structures
- Consider context sensitivity for functions
- Profile before investing in precision
- Choose precision vs speed tradeoff
- Handle function calls carefully
- Consider context sensitivity
- Use flow-insensitive as default

## Related Skills

- `constant-propagation-pass` - Dataflow analysis
- `dead-code-eliminator` - Dead code elimination
- `dataflow-analysis-framework` - Analysis framework
- `escape-analysis` - Uses points-to for heap analysis
- `taint-analysis` - Combines with points-to

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| **Andersen, "Program Analysis and Specialization for the C Programming Language" (PhD thesis, 1994)** | Andersen's inclusion-based analysis |
| **Steensgaard, "Points-to Analysis in Almost Linear Time" (POPL 1996)** | Unification-based analysis |
| **Emami, Ghiya, Hendren, "Context-Sensitive Interprocedural Points-to Analysis" (PLDI 1994)** | Context-sensitive analysis |
| **Landi, "Undecidability of Static Analysis" (LOPLAS 1992)** | Theoretical limits |
| **Hardekopf & Lin, "The Ant and the Grasshopper" (PLDI 2007)** | Fast inclusion-based analysis |

## Tradeoffs and Limitations

### Analysis Approach Tradeoffs

| Approach | Precision | Complexity | Notes |
|----------|-----------|------------|-------|
| **Andersen** | High | O(n³) | Inclusion-based |
| **Steensgaard** | Low | ~O(n) | Unification |
| **Flow-sensitive** | High | Expensive | Per-statement |
| **Flow-insensitive** | Low | Fast | Per-program |

### When NOT to Use This Skill

- For type-safe languages: Reference types make it simpler
- For low-level code: Manual analysis may be needed
- For small programs: May be overkill
- Languages without pointers/references
- When may-alias info is not needed
- Performance-critical compilation (use fast analysis)

### Complexity Considerations

- **Andersen**: O(n³) worst case, practical
- **Steensgaard**: Almost linear
- **Context-sensitive**: Exponential without summarization

### Limitations

- **Undecidability**: Full alias analysis is undecidable
- **Imprecision**: Must-alias vs may-alias trade-off
- **Interprocedural**: Requires call-graph
- **Scalability**: Flow-sensitivity expensive
- **Language features**: Exceptions, reflection complicate
- **Array aliasing**: Hard to handle precisely
- Heap modeling is approximate

## Assessment Criteria

A high-quality implementation should have:

| Criterion | What to Look For |
|-----------|------------------|
| Soundness | Includes all possible targets |
| Precision | Minimizes spurious aliases |
| Efficiency | Reasonable runtime |
| Correctness | Matches expected results |

### Quality Indicators

✅ **Good**: Sound, reasonably precise, efficient
⚠️ **Warning**: Too imprecise (all aliases) or too slow
❌ **Bad**: Unsound (misses possible targets)

## Research Tools & Artifacts

Pointer analysis tools:

| Tool | Application | What to Learn |
|------|-------------|---------------|
| **Soot** | Java | Pointer analysis |
| **WALA** | Java | Framework |
| **LLVM** | C/C++ | Alias analysis |

## Research Frontiers

### 1. Field-Sensitive Analysis
- **Goal**: Per-field precision
- **Approach**: Structure splitting

### 2. Demand-Driven Analysis
- **Goal**: Compute on-demand
- **Approach**: Query-based

## Implementation Pitfalls

| Pitfall | Real Consequence | Solution |
|---------|-----------------|----------|
| **Flow sensitivity** | Imprecision | Use flow-sensitive |
| **Interprocedural** | Missing calls | Build call graph |
| **Imprecision** | Too many aliases | Flow sensitivity |
