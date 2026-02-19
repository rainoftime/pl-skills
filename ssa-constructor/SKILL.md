---
name: ssa-constructor
description: 'Constructs Static Single Assignment form. Use when: (1) Building optimizing
  compilers, (2) Implementing program analysis, (3) Verification.'
version: 1.0.0
tags:
- compiler
- ssa
- optimization
- intermediate-representation
difficulty: intermediate
languages:
- python
- rust
- c++
dependencies: []
---

# SSA Constructor

Converts programs to Static Single Assignment (SSA) form.

## When to Use

- Building optimizing compilers
- Program analysis
- Verification
- Register allocation

## What This Skill Does

1. **Renames variables** - Each definition gets unique name
2. **Inserts φ-functions** - Merge values from branches
3. **Computes dominance** - For φ placement
4. **Optimizes SSA** - After construction

## SSA Form

```
Before (multiple definitions):
  x = 1
  x = 2
  y = x + 1

After (SSA):
  x₁ = 1
  x₂ = 2  
  y₁ = x₂ + 1
```

## Implementation

```python
from dataclasses import dataclass, field
from typing import Dict, List, Set, Optional

@dataclass
class CFGNode:
    """Control flow graph node"""
    id: str
    statements: List = field(default_factory=list)
    predecessors: List['CFGNode'] = field(default_factory=list)
    successors: List['CFGNode'] = field(default_factory=list)
    dom: Set['CFGNode'] = field(default_factory=set)
    idom: Optional['CFGNode'] = None
    df: Set['CFGNode'] = field(default_factory=set)  # Dominance frontier

@dataclass
class Program:
    """Program in SSA form"""
    cfg: Dict[str, CFGNode]
    entry: str

@dataclass
class SSAStmt:
    """SSA statement"""
    pass

@dataclass
class SSADef(SSAStmt):
    """x = y op z"""
    target: str
    op: str
    args: List[str]

@dataclass
class PhiFunc(SSAStmt):
    """φ(x₁, x₂, ...)"""
    target: str
    args: List[tuple[str, str]]  # (value, block)

class SSAConstructor:
    """Convert to SSA form"""
    
    def __init__(self):
        self.version: Dict[str, int] = {}  # variable -> current version
        self.current_version: Dict[str, int] = {}  # per block
        self.phi_inserted: Dict[str, List[str]] = {}  # var -> blocks with phi
    
    def construct(self, cfg: Dict[str, CFGNode], entry: str) -> Program:
        """Convert CFG to SSA"""
        
        # Step 1: Compute dominance
        self.compute_dominance(cfg, entry)
        
        # Step 2: Compute dominance frontier
        self.compute_dominance_frontier(cfg, entry)
        
        # Step 3: Insert φ-functions
        self.insert_phi_functions(cfg)
        
        # Step 4: Rename variables
        self.rename_variables(cfg, entry)
        
        return Program(cfg, entry)
    
    def compute_dominance(self, cfg: Dict[str, CFGNode], entry: str):
        """Compute dominance relationships"""
        
        # Initialize
        for node in cfg.values():
            if node.id == entry:
                node.dom = {node}
            else:
                node.dom = set(cfg.keys())
        
        # Iterative computation
        changed = True
        while changed:
            changed = False
            
            for node in cfg.values():
                if node.id == entry:
                    continue
                
                new_dom = {node}
                for pred in node.predecessors:
                    new_dom &= pred.dom
                new_dom.add(node)
                
                if new_dom != node.dom:
                    node.dom = new_dom
                    changed = True
    
    def compute_dominance_frontier(self, cfg: Dict[str, CFGNode], entry: str):
        """Compute dominance frontier"""
        
        for node in cfg.values():
            node.df = set()
        
        for node in cfg.values():
            if len(node.predecessors) >= 2:
                for pred in node.predecessors:
                    # Walk up dominance tree
                    runner = pred
                    while runner != node.idom and runner != entry:
                        runner.df.add(node.id)
                        runner = runner.idom
    
    def compute_idom(self, cfg: Dict[str, CFGNode], entry: str):
        """Compute immediate dominator"""
        
        for node in cfg.values():
            if node.id == entry:
                node.idom = None
                continue
            
            # IDOM = closest strict dominator
            doms = list(node.dom - {node})
            if doms:
                # Remove any that dominate another
                for d in doms:
                    for other in doms:
                        if d != other and other in cfg[d].dom:
                            doms.remove(d)
                node.idom = doms[0] if doms else None
    
    def insert_phi_functions(self, cfg: Dict[str, CFGNode]):
        """Insert φ-functions at dominance frontiers"""
        
        # Track variables needing φ
        to_process: Dict[str, List[str]] = {}  # var -> blocks
        
        # Find all variables defined
        all_vars = set()
        for node in cfg.values():
            for stmt in node.statements:
                if isinstance(stmt, SSADef):
                    all_vars.add(stmt.target)
        
        for var in all_vars:
            to_process[var] = []
            
            # Initial: blocks where var is defined
            for node in cfg.values():
                for stmt in node.statements:
                    if isinstance(stmt, SSADef) and stmt.target == var:
                        to_process[var].append(node.id)
        
        # Iteratively add φ at DF
        for var, blocks in to_process.items():
            for block_id in blocks:
                block = cfg[block_id]
                for df_block in block.df:
                    if df_block not in self.phi_inserted.get(var, []):
                        # Insert φ
                        cfg[df_block].statements.insert(
                            0,
                            PhiFunc(var, [])
                        )
                        # Add to processing
                        if df_block not in to_process[var]:
                            to_process[var].append(df_block)
```

## Variable Renaming

```python
    def rename_variables(self, cfg: Dict[str, CFGNode], entry: str):
        """Rename variables to SSA"""
        
        self.version = {v: 0 for v in self.get_all_vars()}
        
        self.rename_block(cfg[entry], set())
    
    def rename_block(self, block: CFGNode, seen: Set[str]):
        """Rename variables in block"""
        
        # Create new version map for this block
        block_versions = dict(self.version)
        self.current_version[block.id] = block_versions
        
        new_stmts = []
        
        for stmt in block.statements:
            if isinstance(stmt, PhiFunc):
                # Add arguments from predecessors
                new_args = []
                for pred in block.predecessors:
                    pred_versions = self.current_version.get(pred.id, {})
                    # Use reaching definition
                    v = pred_versions.get(stmt.target, 
                                          self.version.get(stmt.target, 0))
                    new_args.append((f"v_{v}", pred.id))
                
                stmt.args = new_args
            
            if isinstance(stmt, SSADef):
                # Increment version
                self.version[stmt.target] = self.version.get(stmt.target, 0) + 1
                new_name = f"{stmt.target}_{self.version[stmt.target]}"
                
                # Rename args
                new_args = []
                for arg in stmt.args:
                    if arg in self.version:
                        new_args.append(f"{arg}_{self.version[arg]}")
                    else:
                        new_args.append(arg)
                
                new_stmts.append(SSADef(new_name, stmt.op, new_args))
            else:
                new_stmts.append(stmt)
        
        block.statements = new_stmts
        
        # Rename successor blocks
        for succ in block.successors:
            if succ.id not in seen:
                seen.add(succ.id)
                self.rename_block(succ, seen)
```

## SSA to Normal Form

```python
class SSAToNormal:
    """Convert SSA back to normal form"""
    
    def convert(self, ssa_program: Program) -> 'Program':
        """Convert SSA to normal form"""
        
        cfg = ssa_program.cfg
        
        # Identify φ-functions
        phi_funcs = self.find_phi_functions(cfg)
        
        # Create pred list for each φ
        for var, blocks in phi_funcs.items():
            for block_id in blocks:
                block = cfg[block_id]
                phi = self.get_phi(block, var)
                
                # Replace φ with moves
                moves = self.phi_to_moves(phi, block.predecessors)
                block.statements.extend(moves)
                
                # Remove φ
                block.statements.remove(phi)
        
        return ssa_program
    
    def phi_to_moves(self, phi: PhiFunc, preds: List[CFGNode]) -> List:
        """Convert φ to moves"""
        
        moves = []
        
        for (value, pred_id), pred in zip(phi.args, preds):
            moves.append(SSADef(phi.target, 'move', [value]))
        
        return moves
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| **SSA** | Each variable defined once |
| **Versioning** | x → x₁, x₂, ... |
| **φ-function** | Merge at control flow joins |
| **Dominance** | All paths pass through |
| **DF** | Where φ needed |

## Optimization Benefits

- Constant propagation
- Copy propagation
- Dead code elimination
- Register allocation

## Tips

- Compute dominance correctly
- Place φ at dominance frontier
- Handle functions separately
- Consider minimal SSA

## Related Skills

- `constant-propagation-pass` - Dataflow
- `ssa-constructor` - Register allocation
- `common-subexpression-eliminator` - CSE

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| **Cytron et al., "Efficiently Computing Static Single Assignment Form and the Control Dependence Graph" (TOPLAS 1991)** | Original SSA paper |
| **Appel, "Modern Compiler Implementation in ML", Ch. 19 (1998)** | SSA construction algorithms |
| **Cooper & Torczon, "Engineering a Compiler", Ch. 9 (2003)** | Practical SSA implementation |

## Research Tools & Artifacts

SSA implementations in production compilers:

| Compiler | What to Learn |
|----------|---------------|
| **LLVM** | Industrial SSA, optimization passes |
| **GCC** | GIMPLE SSA form |
| **HotSpot JVM** | JVM-level SSA |
| **GraalVM** | Truffle framework |

### Academic/Research

- **SSA Book** (Click & Cooper) - Comprehensive reference
- **Cytron et al.** - Original SSA paper

## Research Frontiers

### 1. SSA Extensions
- **SSA for memory**: Pointer analysis integration
- **SSA for concurrency**: Thread-specific versions
- **SSA for debugging**: Debug info preservation

### 2. SSA Destruction
- **Challenge**: Converting SSA back to normal form
- **Approach**: φ-to-moves conversion, copy propagation
- **Papers**: "SSA Destruction" (Brandt et al.)

## Implementation Pitfalls

| Pitfall | Real Consequence | Solution |
|---------|-----------------|----------|
| **Wrong dominance** | Incorrect φ placement | Use iterative DF computation |
| **Missing φ** | Wrong program semantics | Compute DF correctly |
| **Version explosion** | Too many versions | Use minimal SSA |

### The "Minimal vs Pruned SSA" Tradeoff

- **Minimal SSA**: Insert φ at every DF, may have unused φ
- **Pruned SSA**: Only keep φ for variables used later, fewer φ but needs liveness
