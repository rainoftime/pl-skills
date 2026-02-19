---
name: model-checker
description: 'Implements bounded model checking for finite-state systems. Use when:
  (1) Verifying concurrent programs, (2) Hardware verification, (3) Protocol verification.'
version: 1.0.0
tags:
- verification
- model-checking
- temporal-logic
- state-space
difficulty: advanced
languages:
- python
- ocaml
dependencies: []
---

# Model Checker

Implements bounded model checking using SAT/SMT solvers.

## When to Use

- Concurrent program verification
- Protocol verification  
- Hardware verification
- Bug detection

## What This Skill Does

1. **Encodes transitions** - To SAT/SMT
2. **Unwinds loops** - Bounded exploration
3. **Checks properties** - Safety, liveness
4. **Generates counterexamples** - For violations

## Implementation

```python
from dataclasses import dataclass, field
from typing import Dict, List, Set, Optional
import z3

@dataclass
class State:
    """Program state"""
    pc: int  # Program counter
    vars: Dict[str, int]  # Variables

@dataclass
class Transition:
    """State transition"""
    from_state: State
    to_state: State
    condition: Optional[z3.BoolRef] = None

@dataclass
class Model:
    """Transition system"""
    states: Set[State]
    initial: Set[State]
    transitions: List[Transition]
    variables: List[str]

@dataclass
class Property:
    """Temporal property"""
    pass

@dataclass
class Invariant(Property):
    """Invariant: always P"""
    predicate: z3.BoolRef

@dataclass
class Reachability(Property):
    """Eventually reach: ◇P"""
    predicate: z3.BoolRef

class BoundedModelChecker:
    """Bounded model checker"""
    
    def __init__(self):
        self.solver = z3.Solver()
        self.model: Optional[Model] = None
        self.bound: int = 0
    
    def check(self, model: Model, property: Property, 
              bound: int = 10) -> 'CheckResult':
        """
        Bounded model checking
        
        Returns: (sat/unsat, counterexample if sat)
        """
        
        self.model = model
        self.bound = bound
        
        match property:
            case Invariant(pred):
                return self.check_invariant(pred, bound)
            
            case Reachability(pred):
                return self.check_reachability(pred, bound)
        
        raise ValueError(f"Unknown property: {property}")
    
    def check_invariant(self, invariant: z3.BoolRef, 
                       bound: int) -> 'CheckResult':
        """
        Check invariant: ⊡P (always P)
        
        Encode: ∧_{i=0}^{k} (state_i → P)
        """
        
        self.solver = z3.Solver()
        
        # Create state variables
        state_vars = self.create_state_variables(bound)
        
        # Encode initial state
        self.encode_initial(state_vars[0])
        
        # Encode transitions
        for i in range(bound):
            self.encode_transition(state_vars[i], state_vars[i+1])
        
        # Encode invariant violation
        for i in range(bound + 1):
            violation = z3.Not(self.encode_state_predicate(state_vars[i], invariant))
            self.solver.add(violation)
        
        # Check
        if self.solver.check() == z3.sat:
            model = self.solver.model()
            return CheckResult(
                sat=True,
                counterexample=self.extract_trace(state_vars, model),
                message="Invariant violated"
            )
        
        return CheckResult(
            sat=False,
            counterexample=None,
            message="Invariant holds within bound"
        )
    
    def check_reachability(self, target: z3.BoolRef,
                          bound: int) -> 'CheckResult':
        """
        Check reachability: ◇P
        
        Encode: ∃i. state_i → P
        """
        
        self.solver = z3.Solver()
        
        state_vars = self.create_state_variables(bound)
        self.encode_initial(state_vars[0])
        
        for i in range(bound):
            self.encode_transition(state_vars[i], state_vars[i+1])
        
        # Target reachable
        target_reached = z3.Bool('target_reached')
        for i in range(bound + 1):
            self.solver.add(
                target_reached == self.encode_state_predicate(state_vars[i], target)
            )
        
        self.solver.add(target_reached)
        
        if self.solver.check() == z3.sat:
            model = self.solver.model()
            return CheckResult(
                sat=True,
                counterexample=self.extract_trace(state_vars, model),
                message="Target reachable"
            )
        
        return CheckResult(
            sat=False,
            counterexample=None,
            message="Target not reachable within bound"
        )
    
    def create_state_variables(self, bound: int) -> List[Dict[str, z3.Expr]]:
        """Create symbolic state variables"""
        
        states = []
        
        for i in range(bound + 1):
            state = {}
            for var in self.model.variables:
                state[var] = z3.Int(f"s{i}_{var}")
            states.append(state)
        
        return states
    
    def encode_initial(self, state: Dict[str, z3.Expr]):
        """Encode initial state constraints"""
        
        for init in self.model.initial:
            for var, val in init.vars.items():
                self.solver.add(state[var] == val)
    
    def encode_transition(self, from_state: Dict[str, z3.Expr],
                        to_state: Dict[str, z3.Expr]):
        """Encode transition relation"""
        
        for trans in self.model.transitions:
            # Match: from_state matches trans.from_state
            # Result: to_state matches trans.to_state
            
            conditions = []
            
            for var in self.model.variables:
                # Simple: copy if not changed
                conditions.append(to_state[var] == from_state[var])
            
            # Add transition-specific constraints
            for var, val in trans.to_state.vars.items():
                if var in from_state and from_state[var] != val:
                    conditions.append(to_state[var] == val)
            
            if trans.condition:
                conditions.append(trans.condition)
            
            self.solver.add(z3.Or(conditions))
    
    def encode_state_predicate(self, state: Dict[str, z3.Expr],
                              pred: z3.BoolRef) -> z3.BoolRef:
        """Encode predicate for state"""
        
        # Substitute state variables into predicate
        subst = {z3.Int(var): val for var, val in state.items()}
        
        return z3.substitute(pred, subst)
    
    def extract_trace(self, states: List[Dict[str, z3.Expr]], 
                     model: z3.Model) -> List[Dict[str, int]]:
        """Extract counterexample trace"""
        
        trace = []
        
        for state in states:
            concrete = {}
            for var, expr in state.items():
                val = model.eval(expr)
                concrete[var] = val.as_long()
            trace.append(concrete)
        
        return trace

@dataclass
class CheckResult:
    """Model checking result"""
    sat: bool
    counterexample: Optional[List[Dict[str, int]]]
    message: str
```

## Concurrent Program Verification

```python
class ConcurrentModelChecker:
    """Model checker for concurrent programs"""
    
    def __init__(self):
        self.checker = BoundedModelChecker()
    
    def verify_two_thread(self, program: 'Program', 
                        property: Property) -> CheckResult:
        """
        Verify program with 2 threads
        
        Interleaving semantics:
        - All possible thread schedules
        - Shared memory consistency
        """
        
        # Model as transition system
        model = self.create_model(program)
        
        # Check with increasing bounds
        for bound in range(1, 20):
            result = self.checker.check(model, property, bound)
            
            if result.sat:
                return result
        
        return CheckResult(
            sat=False,
            counterexample=None,
            message="Property holds (or bound too small)"
        )
    
    def create_model(self, program: 'Program') -> Model:
        """Create transition system model"""
        
        # Extract states and transitions
        states = set()
        initial = set()
        transitions = []
        
        # Initial state
        init_state = State(pc=0, vars=program.init_vars)
        initial.add(init_state)
        states.add(init_state)
        
        # Build transitions from CFG
        for stmt in program.statements:
            from_state = State(stmt.from_pc, stmt.from_vars)
            to_state = State(stmt.to_pc, stmt.to_vars)
            
            trans = Transition(from_state, to_state, stmt.condition)
            transitions.append(trans)
            
            states.add(from_state)
            states.add(to_state)
        
        return Model(
            states=states,
            initial=initial,
            transitions=transitions,
            variables=list(program.variables)
        )
```

## Liveness Checking

```python
class LivenessChecker:
    """Check liveness properties"""
    
    def check_liveness(self, model: Model, property: Reachability) -> CheckResult:
        """
        Check: ◇P (eventually P)
        
        Uses fairness constraints
        """
        
        # Check: can we reach P infinitely often?
        # Add fairness: each thread executes infinitely
        
        # For now, simple bounded version
        checker = BoundedModelChecker()
        
        # Try increasingly larger bounds
        for bound in range(1, 50):
            result = checker.check(model, property, bound)
            
            if result.sat:
                return result
        
        return CheckResult(sat=False, message="Property may not hold")
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| **Bounded model checking** | Unwind to bounded depth |
| **SAT/SMT encoding** | Encode to boolean formulas |
| **Counterexample** | Trace to violation |
| **Fairness** | Assumptions about scheduler |

## Properties

| Property | Symbol | Description |
|----------|--------|-------------|
| **Invariant** | ⊡P | Always P |
| **Reachability** | ◇P | Eventually P |
| **Liveness** | □◇P | Infinitely often P |
| **Safety** | □(P → Q) | If P then Q |

## Tips

- Start with small bounds
- Use predicate abstraction
- Handle infinite state with care
- Consider fairness

## Related Skills

- `symbolic-execution-engine` - Symbolic execution
- `weak-memory-model-verifier` - Memory models
- `smt-solver-interface` - SMT solving

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| **Clarke, Grumberg, Kroening, Peled, Veith, "Model Checking" (MIT Press, 2018)** | Definitive textbook on model checking |
| **Biere, Cimatti, Clarke, Zhu, "Symbolic Model Checking without BDDs" (TACAS 1999)** | BMC paper |
| **Ball & Rajamani, "The SLAM Project: Debugging System Software via Static Analysis" (POPL 2002)** | Software model checking |
| **Kurshan, "Computer-Aided Verification of Coordinating Processes" (1994)** | Hardware model checking origins |
| **Holzmann, "The Model Checker SPIN" (IEEE TSE 1997)** | SPIN model checker |

## Tradeoffs and Limitations

### Model Checking Approach Tradeoffs

| Approach | Pros | Cons |
|----------|------|------|
| **Explicit-state** | Simple, complete | State explosion |
| **Symbolic (BDD)** | Handles large state | Can blow up |
| **Bounded (SMT)** | Good for bugs | Can't prove liveness |
| **Predicate abstraction** | Scales to software | Precision loss |

### When NOT to Use Model Checking

- **For large systems**: State explosion; use abstraction
- **For parameterized systems**: Unbounded verification hard
- **For probabilistic systems**: Use probabilistic model checking
- **For real-time**: Use timed automata model checking

### Complexity Considerations

- **Explicit-state**: O(n) states, exponential in variables
- **Symbolic**: Exponential in worst case, often practical
- **BMC**: Linear in bound × state size
- **SMT solving**: NP-hard, but Z3 fast in practice

### Limitations

- **State explosion**: Main bottleneck; exponential in components
- **Infinite state**: Requires abstraction or bounded checking
- **Scalability**: Can't handle large software systems
- **Liveness**: Hard to verify; requires fairness assumptions
- **Counterexample**: May be too long to understand
- **Parameterization**: N-process systems hard

## Research Tools & Artifacts

Model checking tools:

| Tool | Application | What to Learn |
|------|-------------|---------------|
| **SPIN** | Promela | Model checking |
| **CBMC** | C bounded | Bounded verification |
| **BLAST** | C | Predicate abstraction |
| **SLAM** | Windows drivers | Software model checking |
| **Java PathFinder** | Java | Explicit-state |
| **Alloy** | Relational | Lightweight modeling |

### Key Papers

- **Clarke et al.** - Model checking papers
- **Biere et al.** - BMC papers

## Research Frontiers

### 1. Software Model Checking
- **Goal**: Scale to large codebases
- **Approach**: Predicate abstraction, abstraction refinement
- **Tools**: CBMC, ESBMC

## Implementation Pitfalls

| Pitfall | Real Consequence | Solution |
|---------|-----------------|----------|
| **State explosion** | Can't explore all states | Abstraction |
| **Infinite state** | Non-termination | Bounded |
