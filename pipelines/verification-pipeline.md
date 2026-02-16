---
name: verification-pipeline
description: "End-to-end pipeline for program verification using static analysis and theorem proving."
version: "1.0.0"
skills:
  - dataflow-analysis-framework
  - abstract-interpretation-engine
  - symbolic-execution-engine
  - hoare-logic-verifier
  - invariant-generator
---

# Verification Pipeline

This pipeline demonstrates verifying program correctness using multiple analysis techniques.

## Pipeline Steps

```
Source Code → Parser → CFG → Analysis → Verification → Proof
```

## Step 1: Control Flow Graph Construction

**Skill**: `dataflow-analysis-framework`

**Input**: Source code
**Output**: Control Flow Graph (CFG)

```python
# Build CFG from source
cfg = cfg_builder.build(source_code)
# Nodes = basic blocks
# Edges = control flow transitions
```

## Step 2: Abstract Interpretation

**Skill**: `abstract-interpretation-engine`

**Input**: CFG
**Output**: Abstract states at each program point

```python
# Run abstract interpretation
analyzer = AbstractInterpreter(domain=IntervalDomain())
states = analyzer.analyze(cfg)

# states[node] = abstract state at node entry
# Example: {x: [0, 10], y: [-5, 5]}
```

## Step 3: Invariant Generation

**Skill**: `invariant-generator`

**Input**: CFG + Abstract states
**Output**: Loop invariants

```python
# Generate loop invariants
invariants = invariant_gen.generate(cfg, states)
# Example: "x >= 0 && x <= n" at loop header
```

## Step 4: Symbolic Execution

**Skill**: `symbolic-execution-engine`

**Input**: CFG + Preconditions
**Output**: Path conditions and symbolic states

```python
# Run symbolic execution
sym_exec = SymbolicExecutor(solver=z3)
paths = sym_exec.execute(cfg, preconditions)

# For each path:
# - Path condition: symbolic constraints
# - Symbolic state: variable values
```

## Step 5: Hoare Logic Verification

**Skill**: `hoare-logic-verifier`

**Input**: Program + Pre/Post conditions
**Output**: Verification result

```python
# Verify using Hoare logic
result = hoare_verifier.verify(
    program=program,
    pre="x >= 0",
    post="result >= x"
)

if result.valid:
    print("Verification succeeded!")
else:
    print(f"Counterexample: {result.counterexample}")
```

## Complete Example: Verify Binary Search

```python
def verify_binary_search():
    """Verify correctness of binary search."""
    
    # Program specification
    program = """
    int binary_search(int[] arr, int n, int key) {
        int lo = 0, hi = n - 1;
        while (lo <= hi) {
            int mid = lo + (hi - lo) / 2;
            if (arr[mid] == key) return mid;
            if (arr[mid] < key) lo = mid + 1;
            else hi = mid - 1;
        }
        return -1;
    }
    """
    
    # Preconditions
    pre = """
    sorted(arr, n) && n >= 0
    """
    
    # Postconditions
    post = """
    (result >= 0 && arr[result] == key) ||
    (result == -1 && !contains(arr, n, key))
    """
    
    # Loop invariant (generated or provided)
    invariant = """
    0 <= lo && hi < n &&
    (forall i: 0 <= i < lo ==> arr[i] < key) &&
    (forall i: hi < i < n ==> arr[i] > key)
    """
    
    # Build CFG
    cfg = cfg_builder.build(program)
    
    # Run abstract interpretation
    abstract_states = abstract_interpreter.analyze(cfg)
    
    # Generate/verify invariants
    inv_result = invariant_gen.verify(cfg, invariant)
    
    # Symbolic execution for path coverage
    paths = symbolic_executor.execute(cfg)
    
    # Final verification
    result = hoare_verifier.verify(program, pre, post, invariant)
    
    return result

# Result: VERIFIED or COUNTEREXAMPLE
```

## Extensions

- Add `separation-logician` for heap verification
- Add `loop-termination-prover` for termination proofs
- Add `model-checker` for concurrent programs
- Add `coq-proof-assistant` for formal proofs
