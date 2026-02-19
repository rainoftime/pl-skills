---
name: taint-analysis
description: 'Implements taint analysis for security. Use when: (1) Detecting security
  vulnerabilities, (2) Input validation, (3) Information flow.'
version: 1.0.0
tags:
- static-analysis
- taint-analysis
- security
- information-flow
difficulty: intermediate
languages:
- python
dependencies:
- dataflow-analysis-framework
---

# Taint Analysis

Implements taint analysis for tracking untrusted data flow.

## When to Use

- Security vulnerability detection
- SQL injection detection
- XSS detection
- Input validation

## What This Skill Does

1. **Tracks sources** - Untrusted input
2. **Propagates taint** - Through computations
3. **Detects sinks** - Dangerous operations
4. **Handles sanitizers** - Trusted transformations

## Implementation

```python
from dataclasses import dataclass, field
from typing import Dict, List, Set, Optional, Callable
from enum import Enum

class Taint(Enum):
    """Taint status"""
    TAINTED = "tainted"
    UNTAINTED = "untainted"
    UNKNOWN = "unknown"

@dataclass
class TaintLattice:
    """Taint lattice: UNTAINTED < UNKNOWN < TAINTED"""
    
    @staticmethod
    def meet(a: Taint, b: Taint) -> Taint:
        """Meet (more precise)"""
        if a == b:
            return a
        
        if a == Taint.UNTAINTED or b == Taint.UNTAINTED:
            return Taint.UNTAINTED
        
        return Taint.UNKNOWN
    
    @staticmethod
    def join(a: Taint, b: Taint) -> Taint:
        """Join (less precise)"""
        if a == b:
            return a
        
        if a == Taint.TAINTED or b == Taint.TAINTED:
            return Taint.TAINTED
        
        return Taint.UNKNOWN
    
    @staticmethod
    def less_or_equal(a: Taint, b: Taint) -> bool:
        """Partial order"""
        order = [Taint.UNTAINTED, Taint.UNKNOWN, Taint.TAINTED]
        return order.index(a) <= order.index(b)

# Taint environment
class TaintEnvironment(Dict[str, Taint]):
    """Map variables to taint status"""
    
    def meet(self, other: 'TaintEnvironment') -> 'TaintEnvironment':
        """Meet two environments"""
        
        result = TaintEnvironment()
        all_vars = set(self.keys()) | set(other.keys())
        
        for var in all_vars:
            v1 = self.get(var, Taint.UNTAINTED)
            v2 = other.get(var, Taint.UNTAINTED)
            result[var] = TaintLattice.meet(v1, v2)
        
        return result
    
    def join(self, other: 'TaintEnvironment') -> 'TaintEnvironment':
        """Join two environments"""
        
        result = TaintEnvironment()
        all_vars = set(self.keys()) | set(other.keys())
        
        for var in all_vars:
            v1 = self.get(var, Taint.UNTAINTED)
            v2 = other.get(var, Taint.UNTAINTED)
            result[var] = TaintLattice.join(v1, v2)
        
        return result

# Sources and sinks
@dataclass
class Source:
    """Taint source"""
    name: str
    function: str
    return_taint: bool = True

@dataclass
class Sink:
    """Taint sink (dangerous)"""
    name: str
    function: str
    taint_args: List[int]  # Which arguments should be taint-checked

@dataclass
class Sanitizer:
    """Taint sanitizer"""
    name: str
    function: str

# Taint analysis
class TaintAnalysis:
    """Taint analysis"""
    
    def __init__(self):
        self.sources: List[Source] = []
        self.sinks: List[Sink] = []
        self.sanitizers: List[Sanitizer] = []
        self.cfg: Dict[str, 'Stmt'] = {}
        
        # Results
        self.vulnerabilities: List['Vulnerability'] = []
    
    def add_source(self, name: str, function: str):
        """Add taint source"""
        
        self.sources.append(Source(name, function))
    
    def add_sink(self, name: str, function: str, taint_args: List[int]):
        """Add taint sink"""
        
        self.sinks.append(Sink(name, function, taint_args))
    
    def add_sanitizer(self, name: str, function: str):
        """Add taint sanitizer"""
        
        self.sanitizers.append(Sanitizer(name, function))
    
    def analyze(self, program: 'Program') -> List['Vulnerability']:
        """
        Perform taint analysis
        
        Returns: List of vulnerabilities
        """
        
        # Forward analysis
        self.forward_analyze(program)
        
        # Check sinks for taint
        self.check_sinks(program)
        
        return self.vulnerabilities
    
    def forward_analyze(self, program: 'Program'):
        """Forward taint propagation"""
        
        # Worklist
        worklist = list(program.cfg.keys())
        in_env: Dict[str, TaintEnvironment] = {}
        out_env: Dict[str, TaintEnvironment] = {}
        
        # Initialize
        for node in program.cfg:
            in_env[node] = TaintEnvironment()
            out_env[node] = TaintEnvironment()
        
        # Initial: sources are tainted
        entry = program.entry
        for source in self.sources:
            in_env[entry][source.function] = Taint.TAINTED
        
        while worklist:
            node = worklist.pop(0)
            
            # Compute IN: join all predecessors
            preds = program.cfg.predecessors(node)
            if preds:
                in_val = out_env[preds[0]].copy()
                for pred in preds[1:]:
                    in_val = in_val.join(out_env[pred])
            else:
                in_val = TaintEnvironment()
            
            if in_env[node].less_or_equal(in_val):
                # Changed - update and add successors
                in_env[node] = in_val
                
                # Transfer
                out_val = self.transfer(node, program.cfg[node], in_env)
                
                if out_env[node] != out_val:
                    out_env[node] = out_val
                    
                    for succ in program.cfg.successors(node):
                        if succ not in worklist:
                            worklist.append(succ)
    
    def transfer(self, node: str, stmt: 'Stmt', 
                env: TaintEnvironment) -> TaintEnvironment:
        """Apply taint transfer"""
        
        result = TaintEnvironment(env)
        
        match stmt:
            case Assign(x, expr):
                # Propagate taint
                result[x] = self.eval_taint(expr, env)
            
            case Call(func, args):
                # Check if source
                for source in self.sources:
                    if func == source.function:
                        result[func] = Taint.TAINTED
                
                # Check if sanitizer
                for sanitizer in self.sanitizers:
                    if func == sanitizer.function:
                        # Remove taint from arguments
                        for arg in args:
                            result[arg] = Taint.UNTAINTED
            
            case If(cond, then, else_):
                # Both branches
                pass  # Simplified
        
        return result
    
    def eval_taint(self, expr: 'Expr', env: TaintEnvironment) -> Taint:
        """Evaluate expression taint"""
        
        match expr:
            case Const(_):
                return Taint.UNTAINTED
            
            case Var(x):
                return env.get(x, Taint.UNTAINTED)
            
            case BinOp(_, e1, e2):
                t1 = self.eval_taint(e1, env)
                t2 = self.eval_taint(e2, env)
                # If either tainted, result tainted
                return TaintLattice.join(t1, t2)
            
            case Call(func, args):
                # Check function
                for source in self.sources:
                    if func == source.function:
                        return Taint.TAINTED
                
                for sanitizer in self.sanitizers:
                    if func == sanitizer.function:
                        return Taint.UNTAINTED
                
                return Taint.UNKNOWN
        
        return Taint.UNKNOWN
    
    def check_sinks(self, program: 'Program'):
        """Check for taint violations at sinks"""
        
        for node, stmt in program.cfg.items():
            match stmt:
                case Call(func, args):
                    for sink in self.sinks:
                        if func == sink.function:
                            # Check if any tainted argument reaches sink
                            for arg_idx in sink.taint_args:
                                if arg_idx < len(args):
                                    arg = args[arg_idx]
                                    
                                    # Get taint from environment
                                    taint = self.get_variable_taint(arg, program, node)
                                    
                                    if taint == Taint.TAINTED:
                                        self.vulnerabilities.append(Vulnerability(
                                            severity="HIGH",
                                            type=sink.name,
                                            location=node,
                                            description=f"Tainted data reaches {sink.name}"
                                        ))
    
    def get_variable_taint(self, var: str, program: 'Program', 
                         node: str) -> Taint:
        """Get variable taint at node"""
        
        # Simplified: trace back to definition
        # Real implementation: use dataflow analysis
        
        return Taint.UNKNOWN

@dataclass
class Vulnerability:
    """Security vulnerability"""
    severity: str
    type: str
    location: str
    description: str
```

## Taint Domains

| Domain | Precision | Use Case |
|--------|-----------|----------|
| **Tainted/Untainted** | Low | Simple tracking |
| **Tainted/Sanitized/Unknown** | Medium | SQL injection |
| **Multiple sources** | High | Different sensitivity |

## Key Concepts

| Concept | Description |
|---------|-------------|
| **Source** | Where taint originates |
| **Sink** | Where taint matters |
| **Sanitizer** | Removes taint |
| **Propagation** | How taint spreads |

## Applications

- SQL injection
- XSS (cross-site scripting)
- Command injection
- Path traversal

## Tips

- Define sources carefully
- Handle sanitizers correctly
- Consider implicit flows
- Use type qualifiers

## Related Skills

- `dataflow-analysis-framework` - Dataflow
- `information-flow-analyzer` - Information flow
- `alias-and-points-to-analysis` - Pointer analysis

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| **Denning, "A Lattice Model of Secure Information Flow" (CACM 1976)** | Foundational information flow paper |
| **Schwartz et al., "All You Ever Wanted to Know About Dynamic Taint Analysis" (2007)** | Comprehensive survey |
| **Newsome & Song, "Dynamic Taint Analysis for Automatic Detection" (NDSS 2005)** | DTA for vulnerability detection |
| **Haldar et al., "Dynamic Taint Propagation for Java" (ACSAC 2005)** | Taint for Java |

## Tradeoffs and Limitations

### Taint Analysis Approach Tradeoffs

| Approach | Pros | Cons |
|----------|------|------|
| **Static** | No runtime overhead | May over-approximate |
| **Dynamic** | Precise | Missing paths |
| **Hybrid** | Best of both | Complex |

### When NOT to Use Taint Analysis

- **For simple inputs**: Manual review may be faster
- **For encrypted data**: Taint doesn't track encryption
- **For timing channels**: Not detected by taint

### Complexity Considerations

- **Dataflow analysis**: O(n) in program size
- **Interprocedural**: Exponential without summarization
- **Context sensitivity**: Increases complexity

### Limitations

- **Implicit flows**: Taint can leak through control flow
- **Under-approximation**: Dynamic taint misses bugs
- **Over-approximation**: Static taint produces false positives
- **Sanitizer handling**: Complex to get right
- **Aliasing**: Hard to track through pointers
- **Soundness**: Hard to achieve in practice
- **Soundness vs completeness**: Trade-off required

## Research Tools & Artifacts

Taint analysis tools:

| Tool | Application | What to Learn |
|------|-------------|---------------|
| **Infer** | Facebook | Static taint |
| **CodeQL** | GitHub | Query-based |
| **FlowDroid** | Android | Static taint |

## Research Frontiers

### 1. Dynamic Taint Analysis
- **Approach**: Track at runtime
- **Tools**: TaintDroid

## Implementation Pitfalls

| Pitfall | Real Consequence | Solution |
|---------|-----------------|----------|
| **Implicit flows** | Missed leaks | Control flow tracking |
