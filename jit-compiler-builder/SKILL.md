---
name: jit-compiler-builder
description: 'Builds Just-In-Time compilation systems. Use when: (1) Language implementation,
  (2) Dynamic optimization, (3) VM design.'
version: 1.0.0
tags:
- compiler
- jit
- runtime
- optimization
difficulty: advanced
languages:
- rust
- c++
- llvm
dependencies:
- llvm-backend-generator
- ssa-constructor
---

# JIT Compiler Builder

Builds JIT compilation systems for dynamic languages.

## When to Use

- Implementing language runtimes
- Dynamic optimization
- VM design
- Performance optimization

## What This Skill Does

1. **Generates machine code** - From intermediate representation
2. **Handles recompilation** - On hot paths
3. **Optimizes dynamically** - Runtime profiling
4. **Manages memory** - Code allocation

## JIT Strategies

| Strategy | When | Tradeoff |
|----------|------|----------|
| **Eager** | Immediate | Fast first run |
| **Lazy** | On call | Slower first run |
| **Adaptive** | Hot code | Best overall |
| **Multi-level** | Tiered | Best performance |

## Implementation

```python
import struct
import mmap
from typing import Dict, List, Callable, Optional
from dataclasses import dataclass

# Machine code buffer
class CodeBuffer:
    """Executable code buffer"""
    
    def __init__(self, size: int = 64 * 1024):
        self.size = size
        self.buffer = mmap.mmap(-1, size, mmap.ACCESS_WRITE | mmap.ACCESS_EXEC)
        self.cursor = 0
        self.labels: Dict[str, int] = {}
    
    def emit(self, bytes_data: bytes):
        """Emit machine code"""
        
        if self.cursor + len(bytes_data) > self.size:
            raise CodeBufferFull()
        
        self.buffer[self.cursor:self.cursor + len(bytes_data)] = bytes_data
        self.cursor += len(bytes_data)
        
        return self.cursor - len(bytes_data)
    
    def emit_byte(self, b: int):
        return self.emit(bytes([b]))
    
    def emit_word(self, w: int):
        return self.emit(struct.pack('<I', w))
    
    def emit_qword(self, q: int):
        return self.emit(struct.pack('<Q', q))
    
    def get_address(self, offset: int = 0) -> int:
        """Get address of current position + offset"""
        return self.buffer._mmapstart_ + self.cursor + offset
    
    def make_executable(self):
        """Make code executable"""
        import platform
        if platform.system() == 'Linux':
            import ctypes
            libc = ctypes.CDLL('libc.so.6')
            addr = self.buffer._mmapstart_ + self.cursor
            libc.mprotect(addr & ~0xfff, 0x1000, 7)  # rwx

# x86-64 code emission
class X64Emitter:
    """x86-64 code emitter"""
    
    def __init__(self, code: CodeBuffer):
        self.code = code
    
    # Registers
    RAX, RBX, RCX, RDX = 0, 3, 1, 2
    RSI, RDI = 6, 7
    R8, R9, R10, R11 = 8, 9, 10, 11
    RBP, RSP, RIP = 5, 4, 4  # Special
    
    def mov_r64_imm64(self, reg: int, imm: int):
        """mov r64, imm64"""
        # REX.W + B8+rd | imm32
        self.code.emit_byte(0x48 | (reg >> 3))
        self.code.emit_byte(0xB8 | (reg & 7))
        self.code.emit_qword(imm)
    
    def mov_r64_r64(self, dst: int, src: int):
        """mov r64, r64"""
        # REX.W + B8+rd | modrm | ...
        self.code.emit_byte(0x48)
        self.code.emit_byte(0x89)
        self.code.emit_byte(0xC0 | (src << 3) | dst)
    
    def add_r64_r64(self, dst: int, src: int):
        """add r64, r64"""
        self.code.emit_byte(0x48)
        self.code.emit_byte(0x01)
        self.code.emit_byte(0xC0 | (src << 3) | dst)
    
    def ret(self):
        """ret"""
        self.code.emit_byte(0xC3)
    
    def call_r64(self, reg: int):
        """call r64"""
        self.code.emit_byte(0xFF)
        self.code.emit_byte(0xD0 | reg)
```

## Adaptive Optimization

```python
class JITCompiler:
    """Adaptive JIT compiler"""
    
    def __init__(self):
        self.code_buffer = CodeBuffer()
        self.emitter = X64Emitter(self.code_buffer)
        self.compiled: Dict[str, Callable] = {}
        
        # Profiling
        self.call_counts: Dict[str, int] = {}
        self.hot_threshold = 1000
        
        # Compiled code
        self.machine_code: Dict[str, int] = {}
    
    def compile_function(self, ir: 'IRFunction') -> Callable:
        """Compile IR function to machine code"""
        
        # Reset code buffer
        self.code_buffer.cursor = 0
        
        # Generate code
        self.emit_prologue()
        
        for block in ir.blocks:
            self.emit_block(block)
        
        self.emit_epilogue()
        
        # Make executable
        self.code_buffer.make_executable()
        
        # Get function pointer
        addr = self.code_buffer.get_address()
        func = self._create_function_pointer(addr, ir.signature)
        
        self.compiled[ir.name] = func
        return func
    
    def emit_prologue(self):
        """Emit function prologue"""
        # push rbp
        self.emitter.code.emit_byte(0x55)
        # mov rbp, rsp
        self.emitter.mov_r64_r64(self.emitter.RBP, self.emitter.RSP)
        # sub rsp, frame_size
        self.emitter.code.emit_byte(0x48)
        self.emitter.code.emit_byte(0x81)
        self.emitter.code.emit_byte(0xEC)
        self.emitter.code.emit_word(256)  # frame size
    
    def emit_epilogue(self):
        """Emit function epilogue"""
        # add rsp, frame_size
        self.emitter.code.emit_byte(0x48)
        self.emitter.code.emit_byte(0x81)
        self.emitter.code.emit_byte(0xC4)
        self.emitter.code.emit_word(256)
        # pop rbp
        self.emitter.code.emit_byte(0x5D)
        # ret
        self.emitter.ret()
    
    def emit_block(self, block: 'IRBlock'):
        """Emit single block"""
        
        for instr in block.instructions:
            self.emit_instruction(instr)
    
    def emit_instruction(self, instr: 'IRInstruction'):
        """Emit single instruction"""
        
        match instr.op:
            case 'add':
                # add dst, src
                self.emitter.add_r64_r64(instr.dst, instr.src)
            
            case 'mov':
                self.emitter.mov_r64_r64(instr.dst, instr.src)
            
            case 'call':
                self._emit_call(instr.target)
            
            case 'ret':
                self._emit_return()
    
    def _create_function_pointer(self, addr: int, sig):
        """Create callable function pointer"""
        
        import ctypes
        
        # Map return type
        restype = {
            'int': ctypes.c_int64,
            'float': ctypes.c_double,
            'void': None
        }.get(sig.return_type, ctypes.c_int64)
        
        # Map argument types
        argtypes = [
            ctypes.c_int64 for _ in sig.params
        ]
        
        return ctypes.CFUNCTYPE(restype, *argtypes)(addr)
```

## Inline Caching

```python
class InlineCache:
    """Inline cache for polymorphic calls"""
    
    def __init__(self, slot_size: int = 3):
        self.cache: List[Optional[tuple]] = [None] * slot_size
        self.slot_size = slot_size
    
    def lookup(self, key) -> Optional[Callable]:
        """Lookup in cache"""
        
        for entry in self.cache:
            if entry and entry[0] == key:
                return entry[1]
        
        return None
    
    def update(self, key, value):
        """Update cache"""
        
        # Shift entries
        for i in range(self.slot_size - 1, 0, -1):
            self.cache[i] = self.cache[i - 1]
        
        self.cache[0] = (key, value)
    
    def generate_guard(self, emitter: X64Emitter, key):
        """Generate guard code"""
        
        # Compare key with cached value
        # mov rax, [key_location]
        # cmp rax, cached_key
        # jne miss_label
        pass
    
    def generate_miss_handler(self, emitter, key):
        """Generate cache miss handler"""
        
        # Update cache
        # Jump to compiled code
        pass
```

## Trace Compilation

```python
class TraceRecorder:
    """Record and compile hot traces"""
    
    def __init__(self):
        self.traces: Dict[str, List] = {}
        self.current_trace = []
    
    def record(self, instr: 'IRInstruction'):
        """Record instruction in trace"""
        
        # Detect loop boundary
        if instr.is_loop_header:
            if len(self.current_trace) > 10:
                # Compile trace
                self.compile_trace()
            
            self.current_trace = []
        
        self.current_trace.append(instr)
    
    def compile_trace(self):
        """Compile recorded trace"""
        
        # Optimize trace
        optimized = self.optimize_trace(self.current_trace)
        
        # Generate code
        code = self.generate_trace_code(optimized)
        
        # Link into parent
        self.link_trace(code)
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| **JIT** | Compile at runtime |
| **Hot path** | Frequently executed code |
| **Inline cache** | Polymorphic call sites |
| **Trace** | Linear execution path |
| **Tiered** | Multiple compilation levels |
| **Speculation** | Optimize assuming types, deopt if wrong |

## Optimization Levels

| Tier | When | Optimizations |
|------|------|---------------|
| Interpreter | Start | None |
| Baseline JIT | 1000 calls | Basic |
| Optimizing JIT | 10000 calls | Aggressive |

## Tips

- Profile before optimizing
- Use guards for type checks
- Implement inline caches
- Consider trace JIT
- Handle deoptimization

## Related Skills

- `garbage-collector-implementer` - Memory management
- `ssa-constructor` - SSA form for JIT IR
- `llvm-backend-generator` - LLVM ORC JIT

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| **Hölzle, Chambers & Ungar, "Optimizing Dynamically-Typed Object-Oriented Languages With Polymorphic Inline Caches" (ECOOP 1991)** | Foundational inline caching technique from SELF |
| **Hölzle, "Adaptive Optimization for SELF" (PhD Thesis, Stanford 1994)** | Comprehensive adaptive optimization techniques |
| **Gal et al., "Trace-based Just-in-Time Type Specialization for Dynamic Languages" (PLDI 2009)** | Trace JIT methodology |

## Research Tools & Artifacts

JIT implementations:

| Tool | What to Learn |
|------|---------------|
| **LuaJIT** | Trace compiler design, very fast interpreter |
| **GraalVM/Truffle** | Language-agnostic JIT via partial evaluation |
| **V8** | Tiered compilation, speculative optimization |
| **HotSpot JVM** | Production server JIT with C1/C2 tiers |

## Research Frontiers

### 1. Speculative Optimization
- **Approach**: Deoptimization

## Implementation Pitfalls

| Pitfall | Real Consequence | Solution |
|---------|-----------------|----------|
| **Deoptimization bugs** | Wrong code | Careful guards |
