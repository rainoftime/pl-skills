---
name: symbolic-execution-engine
description: 'Builds symbolic execution engines for test generation. Use when: (1)
  Generating tests, (2) Finding bugs, (3) Path exploration.'
version: 1.0.0
tags:
- verification
- symbolic-execution
- smt
- testing
difficulty: advanced
languages:
- python
- z3
dependencies: []
---

# Symbolic Execution Engine

Builds symbolic execution engines for program analysis.

## When to Use

- Automated test generation
- Bug detection
- Path exploration
- Program verification

## What This Skill Does

1. **Creates symbolic values** - Represent inputs symbolically
2. **Explores paths** - Systematic path coverage
3. **Generates constraints** - Path conditions
4. **Handles nonlinearity** - Function summaries

## Key Concepts

### Test Generation

```python
def generate_tests(self, program) -> list[dict]:
    """Generate concrete test cases from paths"""
    
    tests = []
    
    for state in self.paths:
        # Solve for concrete values
        self.solver.push()
        for constraint in state.pc:
            self.solver.add(constraint)
        
        if self.solver.check() == z3.sat:
            model = self.solver.model()
            test = {}
            
            for name, sv in state.env.items():
                if sv.concrete is not None:
                    test[name] = sv.concrete
                else:
                    # Get concrete value from model
                    test[name] = model.eval(sv.expr).as_long()
            
            tests.append(test)
        
        self.solver.pop()
    
    return tests
```

### Loop Handling

```python
def unroll_loop(self, while_node, state: SymbolicState, max_iterations):
    """Unroll loop with bound"""
    
    # Generate loop body paths for each iteration
    for i in range(max_iterations):
        loop_state = self.copy_state(state)
        
        # Check loop condition
        cond_val = self.eval_expr(while_node.cond, loop_state)
        loop_state.add_constraint(cond_val == True)
        
        if not self.is_feasible(loop_state):
            break
        
        # Execute loop body (one iteration)
        self.explore(while_node.body, loop_state)
    
    # Assume loop exits (final condition)
    exit_state = self.copy_state(state)
    cond_val = self.eval_expr(while_node.cond, exit_state)
    exit_state.add_constraint(cond_val == False)
    
    if self.is_feasible(exit_state):
        self.explore(while_node.next, exit_state)
```

### Function Summaries

```python
class FunctionSummary:
    """Summary for function (pre/post)"""
    
    def __init__(self, name, params, pre, post):
        self.name = name
        self.params = params
        self.pre = pre    # Symbolic precondition
        self.post = post  # Symbolic postcondition

class SymbolicExecutorWithSummaries(SymbolicExecutor):
    def __init__(self):
        super().__init__()
        self.summaries = {}
    
    def add_summary(self, name: str, summary: FunctionSummary):
        """Add function summary"""
        self.summaries[name] = summary
    
    def explore_call(self, call_node, state: SymbolicState):
        """Handle function call using summary"""
        
        func_name = call_node.func
        args = call_node.args
        
        if func_name in self.summaries:
            # Use summary
            summary = self.summaries[func_name]
            
            # Check precondition
            self.solver.push()
            for c in state.pc:
                self.solver.add(c)
            
            # Substitute args into precondition
            pre = self.substitute(summary.pre, summary.params, args)
            self.solver.add(pre)
            
            if self.solver.check() == z3.sat:
                # Assume postcondition
                post = self.substitute(summary.post, summary.params, args)
                state.add_constraint(post)
            
            self.solver.pop()
        else:
            # Inline function body
            pass  # Implement inlining
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| **Symbolic value** | Variable with symbolic expr |
| **Path condition** | Constraints on inputs for path |
| **Path explosion** | Exponential number of paths |
| **Constraint solving** | Check path feasibility |
| **Function summary** | Input-output contract |

## Techniques

- **Path merging** - Combine equivalent states
- **Loop bounding** - Limit iterations
- **Lazy initialization** - Delay object creation
- **Concolic testing** - Combine concrete + symbolic

## Tips

- Use constraint caching for efficiency
- Handle arrays carefully
- Consider partial order reduction
- Use test generation for verification

## Related Skills

- `hoare-logic-verifier` - Deductive verification
- `model-checker` - Bounded verification
- `invariant-generator` - Infer loop invariants

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| **King, "Symbolic Execution and Program Testing"** | Original symbolic execution paper (1976) |
| **Cadar & Sen, "Symbolic Execution for Software Testing"** | Modern survey |
| **Cadar, Dunbar & Engler, "KLEE: Unassisted and Automatic Generation of High-Coverage Tests"** | Practical symbolic execution |
| **Godefroid, Klarlund & Sen, "DART: Directed Automated Random Testing"** | Concolic testing |
| **Chipounov et al., "The S2E Platform"** | Selective symbolic execution |

## Tradeoffs and Limitations

### Approach Tradeoffs

| Approach | Pros | Cons |
|----------|------|------|
| **Full symbolic** | Complete exploration | Path explosion |
| **Concolic** | Practical, fast | Misses bugs |
| **Selective** | Scales better | Requires configuration |
| **Under-constrained** | Fast, finds bugs | Unsound |

### When NOT to Use Symbolic Execution

- **For large codebases**: Path explosion; use testing or bounded model checking
- **For concurrent programs**: Use model checking or dedicated tools
- **For numerical code**: Consider abstract interpretation
- **For libraries**: Difficult without harness

### Complexity Considerations

- **Path explosion**: Exponential in number of branches
- **SMT solving**: NP-hard in general; Z3 is fast in practice
- **Constraint solving**: Caching helps significantly
- **Memory modeling**: Complex; approximations needed

### Limitations

- **Path explosion**: Main bottleneck; exponential in branches/loops
- **Environment modeling**: System calls, libraries hard to handle
- **Floating point**: Difficult; often uses approximation
- **Loops**: Must bound or use summarization
- **Parallelism**: Path interleavings explode state space
- **Object creation**: Symbolic memory challenging
- **Solvers**: Can time out on complex constraints

## Assessment Criteria

A high-quality symbolic executor should have:

| Criterion | What to Look For |
|-----------|------------------|
| **Coverage** | Explores all reachable paths |
| **Performance** | Scales to large programs |
| **Solver integration** | Handles constraints efficiently |
| **Memory modeling** | Models heap/arrays correctly |
| **Error detection** | Finds bugs without false positives |
| **Extensibility** | Easy to add new language features |

### Quality Indicators

✅ **Good**: High coverage, fast, finds real bugs
⚠️ **Warning**: Path explosion, timeout issues
❌ **Bad**: Misses bugs, unsound (false negatives)

## Research Tools & Artifacts

Real-world symbolic execution tools:

| Tool | Language | What to Learn |
|------|----------|---------------|
| **KLEE** | C/C++ | LLVM-based, production-quality |
| **angr** | Python | Binary analysis |
| **S2E** | QEMU | Selective execution |
| **Manticore** | Python | Binary analysis |
| **Kuzuu** | Rust | Efficient exploration |
| **SMTInterpol** | Java | Incremental solving |

### Specialized Tools

- **SMT solvers**: Z3, CVC4/5, Boolector
- **Test generation**: PEX (Microsoft), DART
- **Fuzzing integration**: AFLFuzz, libFuzzer

## Research Frontiers

### 1. Symbolic Execution + Fuzzing
- **Approach**: Combine symbolic execution with coverage-guided fuzzing
- **Papers**: "Fuzzing with Code Fragments" (Godefroid)
- **Tools**: SAGE, AFLGo
- **Advantage**: Best of both worlds

### 2. Under-Constrained Symbolic Execution
- **Approach**: Don't check all path constraints
- **Papers**: "Under-Constrained Execution" (Chipounov)
- **Tools**: S2E
- **Advantage**: Faster, finds bugs faster

### 3. Parallel Symbolic Execution
- **Approach**: Distribute path exploration
- **Papers**: "Cloud9: A Distributed Symbolic Execution Engine"
- **Tools**: Cloud9, ClusterKlee
- **Advantage**: Scales to many cores

### 4. Symbolic Execution for Contracts
- **Approach**: Use function contracts/summaries
- **Papers**: "Sound Predicate Abstraction" (Gulavani)
- **Tools**: ESC/Java, JPF

## Implementation Pitfalls

| Pitfall | Real Consequence | Solution |
|---------|-----------------|----------|
| **Path explosion** | Never terminates | Bounding, summarization |
| **Solver timeout** | Incomplete exploration | Time limits, caching |
| **Environment modeling** | Missing bugs | Model libraries |
| **Symbolic memory** | Wrong alias analysis | Memory modeling |
| **Floating point** | Missed bugs | Use floating point theories |

### The "Path Explosion" Problem

The classic challenge:

```
if (a) {       // 2 paths
  if (b) {    // 4 paths
    if (c) {  // 8 paths
      ...
    }
  }
}
```

**Solutions**:
1. Loop bounding: Limit iterations
2. Path merging: Join equivalent states  
3. Priority: Explore likely-bug paths first
4. Summaries: Use function contracts

### The "Environment Modeling" Challenge

System calls can't be symbolically executed:

```python
# Can't execute read() symbolically
def handle_read(state, node):
    # Instead, model the effect
    # read(fd, buf, n) -> returns n bytes
    # Create symbolic buffer
    state.env['buf'] = SymbolicBuffer('buf', n)
```

This is why KLEE uses "external models"!
