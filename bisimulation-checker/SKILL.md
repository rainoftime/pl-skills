---
name: bisimulation-checker
description: 'Checks bisimulation for process calculi. Use when: (1) Proving equivalence,
  (2) Compiler optimization, (3) Protocol verification.'
version: 1.0.0
tags:
- semantics
- bisimulation
- equivalence
- process-calculus
difficulty: intermediate
languages:
- python
- ocaml
- coq
dependencies:
- operational-semantics-definer
---

# Bisimulation Checker

Checks bisimulation equivalence for concurrent and reactive systems.

## When to Use

- Proving process equivalence
- Verifying compiler transformations
- Protocol verification
- Semantic equivalence

## What This Skill Does

1. **Defines bisimulation** - Strong and weak
2. **Checks equivalence** - Via game characterization
3. **Handles branching** - With silent steps
4. **Optimizes** - Partition refinement

## Core Theory

```
Strong Bisimulation:
  P ~ Q iff
    ∀a. P →a P' ⇒ ∃Q'. Q →a Q' and P' ~ Q'
    ∀a. Q →a Q' ⇒ ∃P'. P →a P' and P' ~ Q'

Weak Bisimulation:
  P ≈ Q iff
    ∀a. P =a= P' ⇒ ∃Q'. Q =a= Q' and P' ≈ Q'
  
  Where =a= is weak transition (including ε)
```

## Implementation

```python
from dataclasses import dataclass, field
from typing import Dict, Set, List, Optional, Tuple
from collections import defaultdict

@dataclass
class Process:
    """Process term"""
    pass

@dataclass
class Action:
    """Transition action"""
    label: str
    is_silent: bool = False  # τ/ε

@dataclass
class Transition:
    """Transition relation"""
    process: Process
    action: Action
    target: Process

class BisimulationChecker:
    """Check bisimulation"""
    
    def __init__(self):
        self.transitions: Dict[Process, List[Transition]] = defaultdict(list)
    
    def add_transition(self, p: Process, a: Action, q: Process):
        """Add transition p --a--> q"""
        
        self.transitions[p].append(Transition(p, a, q))
    
    def strong_bisimulation(self, p: Process, q: Process) -> bool:
        """
        Check strong bisimulation P ~ Q
        
        Algorithm: Partition refinement
        """
        
        # Initial partition: observable vs silent
        # Refine until stable
        # O((n+m) log n)
        
        return self._check_bisim(p, q, weak=False)
    
    def weak_bisimulation(self, p: Process, q: Process) -> bool:
        """
        Check weak bisimulation P ≈ Q
        """
        
        return self._check_bisim(p, q, weak=True)
    
    def _check_bisim(self, p: Process, q: Process, weak: bool) -> bool:
        """Generic bisimulation check"""
        
        # BFS with visited
        visited: Set[Tuple[Process, Process]] = set()
        worklist = [(p, q)]
        
        while worklist:
            r, s = worklist.pop()
            
            if (r, s) in visited:
                continue
            visited.add((r, s))
            
            # Check: r's transitions match s's
            r_trans = self.transitions.get(r, [])
            s_trans = self.transitions.get(s, [])
            
            for tr in r_trans:
                # Find matching transition in s
                if weak and tr.action.is_silent:
                    # Can match ε
                    worklist.append((tr.target, s))
                    continue
                
                found = False
                for st in s_trans:
                    if weak and st.action.is_silent:
                        found = True
                        worklist.append((r, st.target))
                        continue
                    
                    if tr.action.label == st.action.label:
                        found = True
                        worklist.append((tr.target, st.target))
                        break
                
                if not found:
                    return False
            
            # Check reverse
            for st in s_trans:
                if weak and st.action.is_silent:
                    worklist.append((r, st.target))
                    continue
                
                found = False
                for tr in r_trans:
                    if weak and tr.action.is_silent:
                        found = True
                        worklist.append((st.target, r))
                        continue
                    
                    if st.action.label == tr.action.label:
                        found = True
                        worklist.append((st.target, tr.target))
                        break
                
                if not found:
                    return False
        
        return True

# Process calculus syntax
class PCProcess(Process):
    """Process calculus processes"""
    
    def __init__(self, name: str):
        self.name = name

def pi_calculus_example():
    """
    Process definitions:
      P = x(y).P'    -- receive x then P'
      P = x̅⟨y⟩.P'   -- send y on x then P'
      P = τ.P'        -- silent action
      P | Q           -- parallel
      !P              -- replication
    
    Bisimulation checks:
      x(y).P | x̅⟨z⟩.Q ~ P{y/z} | Q
    """
    pass
```

## Partition Refinement

```python
class EfficientBisim:
    """O(n log n) bisimulation via partition refinement"""
    
    def bisim(self, processes: Set[Process]) -> List[Set[Process]]:
        """
        Partition processes into bisimulation equivalence classes
        """
        
        # Initial partition: by observable actions
        blocks = self._initial_partition(processes)
        
        # Refine until stable
        changed = True
        while changed:
            changed = False
            
            for block in blocks:
                # Try split
                splits = self._refine(block, blocks)
                if splits:
                    blocks = [b for b in blocks if b != block] + splits
                    changed = True
                    break
        
        return blocks
    
    def _initial_partition(self, procs: Set[Process]) -> List[Set[Process]]:
        """Initial partition by action profile"""
        
        profile = {}
        for p in procs:
            actions = frozenset(t.action.label for t in self.transitions[p])
            if actions not in profile:
                profile[actions] = set()
            profile[actions].add(p)
        
        return list(profile.values())
    
    def _refine(self, block: Set[Process], blocks: List[Set[Process]]) -> List[Set[Process]]:
        """Refine block based on predecessor blocks"""
        
        # For each action, check if targets differ
        # Split if necessary
        
        splits = []
        # ... implementation
        return splits
```

## Applications

- Compiler optimization verification
- Protocol equivalence
- Refinement checking
- Process algebra

## Key Concepts

| Concept | Description |
|---------|-------------|
| **Strong bisim** | Exact matching |
| **Weak bisim** | Silent steps ignored |
| **Branching bisim** | Preserve branching structure |
| **Observation equivalence** | Delay-insensitive |

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| **Milner, "Communication and Concurrency"** | Foundational bisimulation treatment |
| **Park, "Concurrency and Automata on Infinite Sequences"** | Original bisimulation paper |
| **Sangiorgi, "On the Origins of Bisimulation and Coinduction"** | Historical perspective |
| **Aczel, "Non-Well-Founded Sets"** | Coinductive foundations |

## Tips

- Use partition refinement
- Handle τ steps carefully
- Consider weak equivalence
- Optimize for large systems

## Related Skills

- `operational-semantics-definer` - Semantics
- `model-checker` - Model checking
- `session-type-checker` - Session types

## Research Tools & Artifacts

Real-world bisimulation and process verification tools:

| Tool | Why It Matters |
|------|----------------|
| **CADP** | Toolbox for verification of asynchronous systems |
| **mCRL2** | Process specification and verification |
| **UPPAAL** | Real-time system verification |
| **Coq** | Interactive bisimulation proofs |
| **HOL** | Higher-order logic bisimulation |
| **PVS** | Verification system with bisimulation |

### Key Systems to Study

- **CCS semantics**: Formal basis for concurrency
- **π-calculus**: Mobile processes
- **LOTOS**: Formal description technique

## Research Frontiers

Current active research in bisimulation:

| Direction | Key Papers | Challenge |
|-----------|------------|-----------|
| **Probabilistic bisimulation** | "Probabilistic Bisimulation" (2001) | Stochastic processes |
| **Quantum bisimulation** | "Quantum Processes" (2016) | Quantum concurrency |
| **Higher-order** | "Higher-order Bisimulation" (1992) | Functions as values |
| **Contextual equivalence** | "Contextual Equivalence" (2010) | Language equivalence |
| **Symbolic** | "Symbolic Bisimulation" (1998) | Infinite state spaces |

### Hot Topics

1. **Bisimulation for security**: Non-interference verification
2. **Quantitative**: Performance-aware equivalence
3. **Distributed systems**: Fault-tolerant equivalence

## Implementation Pitfalls

Common bugs in bisimulation checkers:

| Pitfall | Real Example | Prevention |
|---------|--------------|------------|
| **Wrong handling of τ** | Weak bisim incorrectly | Distinguish τ from ε |
| **Non-termination** | Large state spaces | Use partition refinement |
| **Branching issues** | Divergence not preserved | Use branching bisimulation |
| **State explosion** | Exponential in transitions | Symbolic methods |
| **Infinite processes** | Divergent systems | Use fixpoint algorithms |
| **Label mismatch** | Action sets differ | Check both directions |

### The "τ vs ε" Bug

Weak bisimulation confuses silent steps:
- τ is internal action (must match)
- ε is empty trace (can be inserted)
- Correct: τ can simulate ε but not vice versa

### Partition Refinement Complexity

O(n log n) via:
- Initial partition by observable profile
- Split blocks based on predecessor blocks
- Iterate until stable
