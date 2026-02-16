---
name: actor-model-implementer
description: 'Implements actor model for concurrent computation. Use when: (1) Building
  concurrent systems, (2) Distributed programming, (3) Fault-tolerant systems.'
version: 1.0.0
tags:
- concurrency
- actor-model
- distributed
- message-passing
difficulty: intermediate
languages:
- python
- rust
- erlang
dependencies: []
---

# Actor Model Implementer

Implements the actor model for concurrent computation.

## When to Use

- Building concurrent/distributed systems
- Implementing fault-tolerant systems
- Modeling reactive systems
- Erlang/Elixir-style concurrency

## What This Skill Does

1. **Creates actors** - Independent computational entities
2. **Handles message passing** - Asynchronous communication
3. **Manages mailboxes** - Message queuing
4. **Implements behaviors** - Actor state machines

## Usage Example

```python
# Create system
system = ActorSystem("example")

# Spawn counter
counter_ref = system.spawn(CounterActor)

# Send messages
counter_ref.tell(10)           # Add 10
counter_ref.tell("get")        # Query count

# Ask pattern
def on_reply(count):
    print(f"Count is: {count}")

# Get reply
future = counter_ref.ask("get")
print(f"Count: {future.result()}")

# Spawn ping-pong
ping = system.spawn(PingPongActor)
pong = system.spawn(PingPongActor)

ping.tell("ping", sender=pong)

# Shutdown
system.stop()
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| **Actor** | Isolated computation with private state |
| **Mailbox** | Message queue |
| **Address** | Reference to actor (PID) |
| **Message passing** | Async, no sharing |
| **Behavior** | Message handler function |
| **Supervision** | Fault handling hierarchy |

## Actor Patterns

- **Fire and forget** - Async send
- **Request-response** - Ask with reply
- **Pipeline** - Chain actors
- **Pub/sub** - Topic-based messaging
- **Aggregator** - Collect results

## Tips

- Keep messages immutable
- Avoid blocking in actors
- Use supervision for fault tolerance
- Consider actor per request for isolation
- Monitor mailbox sizes

## Related Skills

- `software-transactional-memory` - STM concurrency
- `race-detection-tool` - Detect race conditions
- `cps-transformer` - First-class continuations

## Research Tools & Artifacts

Actor model implementations:

| System | Language | What to Learn |
|--------|----------|---------------|
| **Erlang/OTP** | Erlang | Original actor model |
| **Akka** | Scala/Java | Production actors |
| **Erlang/Elixir** | Elixir | Distributed actors |
| **Scala Akka** | Scala | Typed actors |
| **Pony** | Pony | Capabilities-based actors |

### Papers

- **Hewitt et al.** - Original actor model papers
- **Armstrong** - Erlang design papers

## Research Frontiers

### 1. Type-Safe Actors
- **Challenge**: Message type safety
- **Approach**: Typed channels, session types
- **Tools**: Akka Typed, Pony

### 2. Distributed Actor Frameworks
- **Challenge**: Location transparency
- **Approach**: Remoting, cluster management

## Implementation Pitfalls

| Pitfall | Real Consequence | Solution |
|---------|-----------------|----------|
| **Blocking** | Mailbox buildup | Async operations |
| **Shared mutable state** | Race conditions | Immutable messages |
| **Deadlocks** | System halt | Avoid cyclic dependencies |
