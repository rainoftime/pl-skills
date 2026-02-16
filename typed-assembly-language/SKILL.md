---
name: typed-assembly-language
description: 'Verifies low-level code with typed assembly language. Use when: (1)
  Verified compilation, (2) Proof-carrying code, (3) Trustworthy systems.'
version: 1.0.0
tags:
- compiler
- typed-assembly
- low-level
- verification
difficulty: advanced
languages:
- assembly
- coq
dependencies:
- type-checker-generator
---

# Typed Assembly Language

Verifies low-level code using typed assembly language (TAL).

## When to Use

- Verified compilation
- Proof-carrying code
- Low-level verification
- Trustworthy systems

## What This Skill Does

1. **Types low-level** - Registers, memory as typed
2. **Verifies safety** - Type preservation
3. **Handles calls** - Stack and calling conventions
4. **Proves properties** - With Hoare logic

## Core Theory

```
TAL Types:
  int              : Integers
  ptr(τ)           : Pointer to τ
  arr(τ, n)       : Array of n τs  
  code(Γ ⊢ τ)     : Code pointer with type
  tuple(τ₁...τₙ)  : Tuples

Typing Rules:
  r : τ            : Register has type τ
  ρ ⊢ m : τ        : Memory at ρ has type τ
  ⊢ i : τ          : Instruction has type τ
```

## Implementation

```python
from dataclasses import dataclass
from typing import Dict, List, Set, Optional

@dataclass
class TALType:
    """TAL type"""
    pass

@dataclass
class TInt(TALType):
    """Integer type"""
    pass

@dataclass
class TPtr(TALType):
    """Pointer type"""
    elem: TALType

@dataclass
class TCode(TALType):
    """Code pointer type"""
    arg_types: List[TALType]
    ret_type: TALType

@dataclass
class TTuple(TALType):
    """Tuple type"""
    types: List[TALType]

@dataclass
class TArray(TALType):
    """Array type"""
    elem: TALType
    length: int

# Register file
RegFile = Dict[str, TALType]

# Memory: address -> type
Memory = Dict[int, TALType]

@dataclass
class TALInstruction:
    """TAL instruction"""
    pass

@dataclass
class Mov(TALInstruction):
    """mov dst, src"""
    dst: str
    src: str

@dataclass
class Add(TALInstruction):
    """add dst, src1, src2"""
    dst: str
    src1: str
    src2: str

@dataclass
class Load(TALInstruction):
    """load dst, [src + offset]"""
    dst: str
    src: str
    offset: int

@dataclass
class Store(TALInstruction):
    """store [dst + offset], src"""
    dst: str
    offset: int
    src: str

@dataclass
class Call(TALInstruction):
    """call addr"""
    target: str

@dataclass
class Ret(TALInstruction):
    """ret"""
    pass

@dataclass
class Branch(TALInstruction):
    """beq r, label"""
    cond: str
    target: str

class TALChecker:
    """TAL type checker"""
    
    def __init__(self):
        self.registers: RegFile = {}
        self.memory: Memory = {}
        self.code_types: Dict[str, TCode] = {}
    
    def check_instruction(self, instr: TALInstruction, 
                         env: RegFile) -> RegFile:
        """Check instruction, return new register types"""
        
        match instr:
            case Mov(dst, src):
                # Copy type
                if src in env:
                    return {**env, dst: env[src]}
                raise TypeError(f"Unknown register: {src}")
            
            case Add(dst, src1, src2):
                # Integer addition
                if (src1 in env and src2 in env and
                    isinstance(env[src1], TInt) and
                    isinstance(env[src2], TInt)):
                    return {**env, dst: TInt()}
                raise TypeError("Non-integer in add")
            
            case Load(dst, src, offset):
                # Load from memory
                if src in env and isinstance(env[src], TPtr(elem)):
                    addr_type = self.memory.get(offset, elem)
                    return {**env, dst: addr_type}
                raise TypeError("Invalid load")
            
            case Store(dst, offset, src):
                # Store to memory
                if dst in env and src in env:
                    self.memory[offset] = env[src]
                    return env
                raise TypeError("Invalid store")
            
            case Call(target):
                # Check code type
                if target in self.code_types:
                    # Assume function returns unit for simplicity
                    return {**env}
                raise TypeError(f"Unknown function: {target}")
            
            case Ret():
                # Return, restore caller state
                return {}
            
            case Branch(cond, target):
                # Check condition is boolean/integer
                if cond in env:
                    return env
                raise TypeError(f"Unknown register: {cond}")
        
        return env
```

## Heap Allocation

```python
class TALHeap:
    """TAL with heap allocation"""
    
    def __init__(self):
        self.heap: Dict[int, tuple] = {}
        self.next_addr = 0x1000
    
    def malloc(self, size: int, layout: TTuple) -> TPtr:
        """Allocate heap object"""
        
        addr = self.next_addr
        self.next_addr += size
        
        # Store layout info
        self.heap[addr] = ('obj', layout)
        
        return TPtr(layout)
    
    def check_heap_access(self, ptr: TPtr, offset: int) -> TALType:
        """Check heap access type"""
        
        if isinstance(ptr.elem, TTuple):
            # Check field type
            field_idx = offset // 8  # Assume 8-byte fields
            if field_idx < len(ptr.elem.types):
                return ptr.elem.types[field_idx]
        
        raise TypeError("Invalid heap access")
```

## Verified Compilation

```python
class VerifiedCompiler:
    """Compile and verify"""
    
    def __init__(self):
        self.tal_checker = TALChecker()
    
    def compile_and_verify(self, high_level: 'Expr') -> bool:
        """
        Compile high-level to TAL and verify
        """
        
        # 1. Compile to intermediate representation
        ir = self.compile_to_ir(high_level)
        
        # 2. Generate TAL code
        tal_code = self.generate_tal(ir)
        
        # 3. Add type annotations
        typed_tal = self.annotate_types(tal_code)
        
        # 4. Verify types
        return self.verify(typed_tal)
    
    def verify(self, tal_code: List[TALInstruction]) -> bool:
        """Verify TAL type safety"""
        
        env = {}
        
        for instr in tal_code:
            try:
                env = self.tal_checker.check_instruction(instr, env)
            except TypeError as e:
                print(f"Type error: {e}")
                return False
        
        return True
```

## Proof-Carrying Code

```python
class PCChecker:
    """Proof-carrying code verification"""
    
    def __init__(self):
        self.policy = SafetyPolicy()
    
    def verify_pcc(self, code: bytes, proof: bytes) -> bool:
        """
        Verify proof-carrying code
        """
        
        # 1. Extract safety policy
        policy = self.extract_policy(code)
        
        # 2. Verify proof
        proof_valid = self.verify_proof(policy, proof)
        
        if not proof_valid:
            return False
        
        # 3. Execute trusted
        return self.execute_trusted(code)
    
    def extract_policy(self, code: bytes) -> SafetyPolicy:
        """Extract safety policy from code"""
        
        # Read type annotations
        # Build policy
        return self.policy
    
    def verify_proof(self, policy: SafetyPolicy, 
                    proof: bytes) -> bool:
        """Verify proof respects policy"""
        
        # Simple: check proof format
        # Real: verify with proof assistant
        return len(proof) > 0
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| **Type preservation** | Well-typed → well-typed |
| **Memory safety** | No invalid accesses |
| **Control flow** | Calls/returns typed |
| **Subtyping** | Pointer subtyping |

## Properties

| Property | Description |
|----------|-------------|
| **Type safety** | No type errors |
| **Memory safety** | Bounds checked |
| **Control safety** | Valid calls/returns |
| **Non-interference** | No info leak |

## Tips

- Use static verification
- Check all paths
- Handle exceptions
- Consider relaxed models

## Related Skills

- `coq-proof-assistant` - Proof assistant
- `ssa-constructor` - SSA form
- `garbage-collector-implementer` - Runtime

## Research Tools & Artifacts

Real-world TAL systems:

| Tool | Why It Matters |
|------|----------------|
| **TAL/T** | Typed assembly language |
| **SPARC TAL** | SPARC architecture |
| **Cool** | Verified compiler |
| **CertiCoq** | Verified Coq compiler |

### Key Systems

- **Coq**: Proof assistant
- **CakeML**: Verified compiler

## Research Frontiers

Current TAL research:

| Direction | Key Papers | Challenge |
|-----------|------------|-----------|
| **Verification** | "Verified Compilation" | End-to-end |
| **PCC** | "Proof-carrying Code" | Proofs |

### Hot Topics

1. **Wasm verification**: WebAssembly typing
2. **RISC-V TAL**: New architecture

## Implementation Pitfalls

Common TAL bugs:

| Pitfall | Real Example | Prevention |
|---------|--------------|------------|
| **Type preservation** | Wrong type | Verify |
