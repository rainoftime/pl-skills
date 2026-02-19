---
name: session-type-checker
description: 'Implements session types for communication protocols. Use when: (1)
  Verifying communication protocols, (2) Distributed systems, (3) Type-safe message
  passing.'
version: 1.0.0
tags:
- type-systems
- concurrency
- session-types
- communication
difficulty: advanced
languages:
- python
- haskell
dependencies:
- linear-type-implementer
---

# Session Type Checker

Implements session types for verifying communication protocols.

## When to Use

- Distributed systems verification
- Protocol verification
- Message passing concurrency
- Type-safe communication

## What This Skill Does

1. **Defines session types** - Communication protocols as types
2. **Verifies protocols** - Ensure correct message sequences
3. **Handles branching** - Choice types
4. **Provides linearity** - Session linearity

## Core Theory

```
Session Types:
  !T.S    : Send T, then continue with S
  ?T.S    : Receive T, then continue with S
  ⊕{l₁:S₁, l₂:S₂}  : External choice (client)
  &{l₁:S₁, l₂:S₂}  : Internal choice (server)
  end     : Session terminated
  μX.S    : Recursive session
```

## Implementation

```python
from dataclasses import dataclass
from typing import Optional, Dict, List, Set

@dataclass
class SessionType:
    """Session type"""
    pass

@dataclass
class Send(SessionType):
    """Send: !T.S"""
    typ: 'Type'
    cont: SessionType

@dataclass
class Recv(SessionType):
    """Receive: ?T.S"""
    typ: 'Type'
    cont: SessionType

@dataclass
class Choice(SessionType):
    """External choice: ⊕{l₁:S₁, l₂:S₂}"""
    branches: Dict[str, SessionType]

@dataclass
class Branch(SessionType):
    """Internal choice: &{l₁:S₁, l₂:S₂}"""
    branches: Dict[str, SessionType]

@dataclass  
class End(SessionType):
    """Termination"""
    pass

@dataclass
class RecVar(SessionType):
    """Recursive variable: μX.S"""
    name: str
    body: SessionType

# Process calculus
@dataclass
class Process:
    pass

@dataclass
class SendProcess(Process):
    """c!v; P"""
    channel: str
    value: 'Value'
    cont: Process

@dataclass
class RecvProcess(Process):
    """c?x; P"""
    channel: str
    var: str
    cont: Process

@dataclass
class SelectProcess(Process):
    """c⊕l; P"""
    channel: str
    label: str
    cont: Process

@dataclass
class OfferProcess(Process):
    """c&{l₁:P₁, l₂:P₂}"""
    channel: str
    branches: Dict[str, Process]

@dataclass
class ParProcess(Process):
    """P | Q"""
    left: Process
    right: Process

@dataclass
class NilProcess(Process):
    """0 (terminated)"""
    pass

class SessionTypeChecker:
    """Session type checker"""
    
    def __init__(self):
        self.session_env: Dict[str, SessionType] = {}
        self.channel_env: Dict[str, str] = {}  # channel -> session type
    
    def check_process(self, proc: Process, expected: SessionType) -> bool:
        """Check process conforms to session type"""
        
        match proc, expected:
            case NilProcess(), End():
                return True
            
            case SendProcess(ch, val, cont), Send(t, cont_type):
                # Check value type
                if not self.check_value(val, t):
                    return False
                # Check continuation
                return self.check_process(cont, cont_type)
            
            case RecvProcess(ch, var, cont), Recv(t, cont_type):
                # Check continuation with bound variable
                new_env = {var: t}
                return self.check_process(cont, cont_type)
            
            case SelectProcess(ch, label, cont), Choice(branches):
                if label not in branches:
                    return False
                return self.check_process(cont, branches[label])
            
            case OfferProcess(ch, branches), Branch(exp_branches):
                # All branches must conform
                for label, proc in branches.items():
                    if label not in exp_branches:
                        return False
                    if not self.check_process(proc, exp_branches[label]):
                        return False
                return True
            
            case ParProcess(p1, p2), _:
                # Split session type
                # Use session splitting (⊗)
                s1, s2 = self.split_type(expected)
                return (self.check_process(p1, s1) and 
                        self.check_process(p2, s2))
        
        return False
    
    def split_type(self, s: SessionType) -> tuple[SessionType, SessionType]:
        """Split session type for parallel composition"""
        
        match s:
            case Send(t, cont):
                s1, s2 = self.split_type(cont)
                return (Send(t, s1), s2)
            
            case Recv(t, cont):
                s1, s2 = self.split_type(cont)
                return (Recv(t, s1), s2)
            
            case End():
                # Cannot split terminated session
                raise ValueError("Cannot split end")
            
            case _:
                # For complex types, need proper splitting
                return (s, s)
```

## Duality

```python
def dual(s: SessionType) -> SessionType:
    """Compute dual (opposite endpoint)"""
    
    match s:
        case Send(t, cont):
            return Recv(t, dual(cont))
        
        case Recv(t, cont):
            return Send(t, dual(cont))
        
        case Choice(branches):
            return Branch({l: dual(s) for l, s in branches.items()})
        
        case Branch(branches):
            return Choice({l: dual(s) for l, s in branches.items()})
        
        case End():
            return End()
        
        case RecVar(name, body):
            return RecVar(name, dual(body))
```

## Example Protocol

```python
# Protocol: Client requests, Server responds
# Client: !Request. ?Response.end
# Server: ?Request. !Response.end

client_protocol = Send(RequestType(), Recv(ResponseType(), End()))
server_protocol = Recv(RequestType(), Send(ResponseType(), End()))

# They are duals!
assert dual(server_protocol) == client_protocol

# Client process
client = SendProcess(
    "c", 
    Request("get_data"),
    RecvProcess("c", "r", NilProcess())
)

# Type check
checker = SessionTypeChecker()
assert checker.check_process(client, client_protocol)
```

## Session Type Inference

```python
class SessionInference:
    """Infer session types from processes"""
    
    def infer(self, proc: Process) -> SessionType:
        """Infer session type for process"""
        
        match proc:
            case NilProcess():
                return End()
            
            case SendProcess(ch, val, cont):
                t = self.infer_value(val)
                s = self.infer(cont)
                return Send(t, s)
            
            case RecvProcess(ch, var, cont):
                t = self.infer_var_type(var)
                s = self.infer(cont)
                return Recv(t, s)
            
            case ParProcess(p1, p2):
                s1 = self.infer(p1)
                s2 = self.infer(p2)
                # Compose sessions
                return self.compose(s1, s2)
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| **Duality** | Sender ↔ Receiver |
| **Session linearity** | One use per session |
| **Branching** | Choice types |
| **Recursion** | μ-binders |

## Properties

| Property | Description |
|----------|-------------|
| **Type safety** | No runtime errors |
| **Protocol fidelity** | Follows spec |
| **Deadlock freedom** | No circular dependencies |
| **Completeness** | All sessions terminate |

## Tips

- Use duality for endpoint checking
- Handle recursion carefully
- Consider session subtyping
- Implement error handling

## Related Skills

- `linear-type-implementer` - Linear types
- `actor-model-implementer` - Actor concurrency
- `software-transactional-memory` - STM

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| **Honda, "Types for Dyadic Interaction" (CONCUR 1993)** | Original session types paper |
| **Honda, Yoshida & Carbone, "Multiparty Asynchronous Session Types" (POPL 2007)** | Multiparty session types |
| **Gay & Hole, "Subtyping for Session Types" (Acta Informatica 2005)** | Session subtyping |
| **Bettini et al., "Global Escape in Multiparty Sessions" (POPL 2008)** | Multiparty protocols |
| **Yoshida & Vasconcelos, "Language Primitives and Type Theory for Communication-Based Programming" (2007)** | Session type primitives |

## Tradeoffs and Limitations

### Type System Tradeoffs

| Approach | Pros | Cons |
|----------|------|------|
| **Binary sessions** | Simple, well-understood | Limited to two parties |
| **Multiparty** | Global specification | Complex choreography |
| **Choiceless** | Simpler | Less expressive |

### When NOT to Use Session Types

- **For shared-state concurrency**: Use locks/STM instead
- **For simple request-response**: REST may suffice
- **For static verification**: Runtime checks may be cheaper

### Complexity Considerations

- **Type checking**: Linear in program size
- **Type inference**: NP-hard in general
- **Session subtyping**: Coinductive; expensive

### Limitations

- **Deadlock**: Not automatically prevented; requires global progress
- **Session initiation**: Complex in practice
- **Error handling**: Sessions can get stuck
- **Runtime overhead**: Channel creation cost
- **Partiality**: Mixed sessions hard to type
- **Distribution**: Network failures not handled

## Research Tools & Artifacts

Session type implementations:

| Tool | Language | What to Learn |
|------|----------|---------------|
| **Scribble** | Java | Protocol design |
| **Odin** | Haskell | Session types |

## Research Frontiers

### 1. Multiparty Session Types
- **Goal**: Global protocol specification

## Implementation Pitfalls

| Pitfall | Real Consequence | Solution |
|---------|-----------------|----------|
| **Deadlock** | Stuck processes | Global progress |
