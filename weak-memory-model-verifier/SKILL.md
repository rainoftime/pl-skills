---
name: weak-memory-model-verifier
description: 'Verifies programs under weak memory models. Use when: (1) Concurrent
  verification, (2) Low-level systems, (3) Multiprocessor correctness.'
version: 1.0.0
tags:
- verification
- memory-models
- concurrency
- relaxed
difficulty: advanced
languages:
- python
- coq
dependencies:
- model-checker
---

# Weak Memory Model Verifier

Verifies programs under weak memory models (x86, ARM, POWER, C/C++11).

## When to Use

- Concurrent systems verification
- Low-level systems programming
- Multiprocessor correctness
- Compiler optimization

## What This Skill Does

1. **Models memory orderings** - Sequential consistency to relaxed
2. **Verifies correctness** - Under different models
3. **Detects races** - Data races under weak models
4. **Synthesizes fences** - Add necessary memory barriers

## Memory Models

```
Strength ordering:
  
  SC (Sequential Consistency)
    ↓
  TSO (Total Store Order) - x86
    ↓
  PSO (Partial Store Order) - SPARC
    ↓
  RMO (Relaxed Memory Order) - ARM/Power
    ↓
  C/C++11 (Release/Acquire)
```

## Implementation

```python
from dataclasses import dataclass, field
from typing import Dict, List, Set, Optional, Tuple
from enum import Enum
import itertools

class MemoryOrder(Enum):
    """C11/C++11 memory orderings"""
    RELAXED = "relaxed"
    CONSUME = "consume"
    ACQUIRE = "acquire"
    RELEASE = "release"
    ACQ_REL = "acq_rel"
    SEQ_CST = "seq_cst"

@dataclass
class Event:
    """Memory event"""
    id: int
    thread: str
    kind: str  # read, write, fence, lock, unlock
    addr: str
    value: Optional[int] = None
    order: MemoryOrder = MemoryOrder.SEQ_CST
    po_before: List = field(default_factory=list)  # Program order
    rf_before: List = field(default_factory=list)  # Reads from
    mo_before: List = field(default_factory=list)  # Modification order

@dataclass
class Execution:
    """Program execution"""
    events: List[Event]
    threads: Set[str]
    synchronization: List[Event] = field(default_factory=list)

class WeakMemoryVerifier:
    """Verify programs under weak memory models"""
    
    def __init__(self, model: str = "c11"):
        self.model = model
        self.relations = {}
    
    def verify(self, execution: Execution) -> bool:
        """
        Verify execution is valid under memory model
        
        Returns True if execution is consistent
        """
        
        # Compute required relations
        self.compute_relations(execution)
        
        # Check for cycles
        return not self.has_cycle()
    
    def compute_relations(self, execution: Execution):
        """Compute memory model relations"""
        
        # Program order (po)
        self.relations['po'] = self.compute_program_order(execution)
        
        # Synchronizes-with (sw)
        self.relations['sw'] = self.comput_synchronizes_with(execution)
        
        # Happens-before (hb)
        self.relations['hb'] = self.compute_happens_before(execution)
        
        # Reads-from (rf)
        self.relations['rf'] = self.compute_reads_from(execution)
        
        # Modification order (mo)
        self.relations['mo'] = self.compute_modification_order(execution)
    
    def compute_program_order(self, execution: Execution) -> Dict:
        """Compute program order relations"""
        
        po = {}
        
        for thread in execution.threads:
            events = [e for e in execution.events if e.thread == thread]
            
            for i, e1 in enumerate(events):
                for e2 in events[i+1:]:
                    po[(e1.id, e2.id)] = True
        
        return po
    
    def comput_synchronizes_with(self, execution: Execution) -> Dict:
        """
        Compute synchronizes-with relations
        
        Release (A) → Acquire (B) if:
        1. A writes to x, B reads from x
        2. B reads value written by A
        3. Memory order ensures visibility
        """
        
        sw = {}
        
        for rel in execution.synchronization:
            # Lock/unlock pairs
            if rel.kind == 'unlock':
                for other in execution.events:
                    if (other.kind == 'lock' and 
                        other.addr == rel.addr and
                        self.happens_before(rel, other)):
                        sw[(rel.id, other.id)] = True
            
            # Release/acquire
            if rel.kind == 'write' and rel.order == MemoryOrder.RELEASE:
                for read in execution.events:
                    if (read.kind == 'read' and
                        read.addr == rel.addr and
                        read.value == rel.value and
                        read.order in (MemoryOrder.ACQUIRE, 
                                      MemoryOrder.SEQ_CST)):
                        # Check reads-from
                        if (rel.id, read.id) in self.relations.get('rf', {}):
                            sw[(rel.id, read.id)] = True
        
        return sw
    
    def compute_happens_before(self, execution: Execution) -> Dict:
        """Compute happens-before (po ∪ sw)"""
        
        hb = {}
        
        # Union of po and sw
        for pair in self.relations.get('po', {}):
            hb[pair] = True
        for pair in self.relations.get('sw', {}):
            hb[pair] = True
        
        # Transitive closure
        changed = True
        while changed:
            changed = False
            for (a, b) in list(hb.keys()):
                for (c, d) in list(hb.keys()):
                    if b == c and (a, d) not in hb:
                        hb[(a, d)] = True
                        changed = True
        
        return hb
    
    def compute_reads_from(self, execution: Execution) -> Dict:
        """Compute reads-from relation"""
        
        rf = {}
        
        for read in execution.events:
            if read.kind == 'read':
                # Find write this reads from
                for write in execution.events:
                    if (write.kind == 'write' and
                        write.addr == read.addr and
                        write.value == read.value):
                        rf[(write.id, read.id)] = True
        
        return rf
    
    def compute_modification_order(self, execution: Execution) -> Dict:
        """Compute modification order for each address"""
        
        mo = {}
        
        # For each address, total order of writes
        writes_by_addr: Dict[str, List[Event]] = {}
        
        for e in execution.events:
            if e.kind == 'write':
                if e.addr not in writes_by_addr:
                    writes_by_addr[e.addr] = []
                writes_by_addr[e.addr].append(e)
        
        for addr, writes in writes_by_addr.items():
            for i, w1 in enumerate(writes):
                for w2 in writes[i+1:]:
                    mo[(w1.id, w2.id)] = True
        
        return mo
    
    def has_cycle(self) -> bool:
        """Check for cycles in hb ∪ rf ∪ mo"""
        
        # Build graph
        edges = set()
        
        # Add hb edges
        edges.update(self.relations.get('hb', {}).keys())
        
        # Add rf edges
        edges.update(self.relations.get('rf', {}).keys())
        
        # Add mo edges  
        edges.update(self.relations.get('mo', {}).keys())
        
        # Check for cycles using DFS
        graph = {}
        for (src, dst) in edges:
            if src not in graph:
                graph[src] = []
            graph[src].append(dst)
        
        visited = set()
        rec_stack = set()
        
        def dfs(node):
            visited.add(node)
            rec_stack.add(node)
            
            for neighbor in graph.get(node, []):
                if neighbor not in visited:
                    if dfs(neighbor):
                        return True
                elif neighbor in rec_stack:
                    return True
            
            rec_stack.remove(node)
            return False
        
        for node in graph:
            if node not in visited:
                if dfs(node):
                    return True
        
        return False
```

## Data Race Detection

```python
class DataRaceDetector:
    """Detect data races under weak memory models"""
    
    def __init__(self, model: str = "c11"):
        self.model = model
        self.verifier = WeakMemoryVerifier(model)
    
    def detect_races(self, execution: Execution) -> List[Tuple[Event, Event]]:
        """
        Detect data races
        
        A data race occurs when:
        1. Two events access same memory location
        2. At least one is a write
        3. They are not ordered by happens-before
        """
        
        races = []
        
        # Group by address
        by_addr: Dict[str, List[Event]] = {}
        for e in execution.events:
            if e.kind in ('read', 'write'):
                if e.addr not in by_addr:
                    by_addr[e.addr] = []
                by_addr[e.addr].append(e)
        
        # Check each address
        for addr, events in by_addr.items():
            for e1, e2 in itertools.combinations(events, 2):
                # Must have one write
                if e1.kind == 'read' and e2.kind == 'read':
                    continue
                
                # Check if ordered
                self.verifier.compute_relations(execution)
                hb = self.verifier.relations.get('hb', {})
                
                if not hb.get((e1.id, e2.id)) and not hb.get((e2.id, e1.id)):
                    races.append((e1, e2))
        
        return races
```

## Fence Synthesis

```python
class FenceSynthesizer:
    """Synthesize memory fences to ensure correctness"""
    
    def synthesize(self, program: 'Program') -> List[str]:
        """
        Add necessary fences to program
        
        Returns list of fence locations
        """
        
        executions = self.generate_executions(program)
        fence_points = set()
        
        for execution in executions:
            # Find violations
            verifier = WeakMemoryVerifier(self.model)
            
            if not verifier.verify(execution):
                # Find missing fences
                violations = self.find_violations(execution, verifier)
                
                for v in violations:
                    fence_points.add(v.location)
        
        return list(fence_points)
    
    def find_violations(self, execution: Execution, 
                       verifier: WeakMemoryVerifier) -> List:
        """Find where fences are needed"""
        
        violations = []
        
        # Check for critical pairs
        for read in execution.events:
            if read.kind != 'read':
                continue
            
            for write in execution.events:
                if write.kind != 'write':
                    continue
                
                if read.addr != write.addr:
                    continue
                
                # Check if there's a race
                hb = verifier.relations.get('hb', {})
                
                if not hb.get((write.id, read.id)):
                    violations.append(Violation(
                        location=read,
                        reason="Missing fence between write and read"
                    ))
        
        return violations
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| **Sequential Consistency** | Total order of all operations |
| **TSO** | Store buffer, writes reorder after reads |
| **Release/Acquire** | Partial ordering |
| **Happens-before** | Partial order |
| **Synchronizes-with** | Cross-thread ordering |

## x86 vs ARM

| Feature | x86 (TSO) | ARM (RMO) |
|---------|-----------|------------|
| Store buffer | Yes | Yes |
| Load reorder | No | Yes |
| Store reorder | No | Yes |
| Fences needed | Rare | Common |

## Tips

- Use verification tools (CBMC, SPIN)
- Model-check for race conditions
- Add minimal fences
- Test on weak model

## Related Skills

- `race-detection-tool` - Standard race detection
- `software-transactional-memory` - STM
- `weak-memory-model-verifier` - Verify concurrency

## Research Tools & Artifacts

Memory model tools:

| Tool | What to Learn |
|------|---------------|
| **CBMC** | Bounded verification |
| **CPG** | Cat |

## Research Frontiers

### 1. Formal Verification
- **Goal**: Prove memory model correctness

## Implementation Pitfalls

| Pitfall | Real Consequence | Solution |
|---------|-----------------|----------|
| **Races** | UB | Add fences |
