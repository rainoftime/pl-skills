---
name: message-passing-system
description: "Implement message passing concurrency models like actors and CSP channels."
version: "1.0.0"
tags: [concurrency, actors, channels, oopsla]
difficulty: intermediate
languages: [rust, go, python]
dependencies: [concurrency-verifier, actor-model-implementer]
---

# Message Passing System

Message passing is a concurrency model where processes/actors communicate by sending messages rather than sharing memory. It avoids many concurrency bugs by design.

## When to Use This Skill

- Building distributed systems
- Avoiding shared-state concurrency bugs
- Implementing actor-based architectures
- Event-driven systems
- Microservices communication

## What This Skill Does

1. **Channel Implementation**: Create typed message channels
2. **Actor Model**: Implement actors with mailboxes
3. **Select/Alt**: Wait on multiple channels
4. **Backpressure**: Handle slow consumers
5. **Message Ordering**: Ensure message ordering guarantees

## Key Concepts

| Concept | Description |
|---------|-------------|
| Channel | Typed conduit for messages |
| Actor | Entity with mailbox and behavior |
| Select | Wait on multiple channels |
| Backpressure | Handle slow consumers |
| Rendezvous | Synchronous message passing |

## Tips

- Use buffered channels for throughput
- Use unbuffered for synchronization
- Implement graceful shutdown
- Handle message ordering carefully
- Consider message delivery guarantees

## Common Use Cases

- Actor-based systems (Akka, Orleans)
- Microservices communication
- Event streaming
- Pipeline processing
- GUI event handling

## Related Skills

- `actor-model-implementer` - Actor foundations
- `lock-free-data-structure` - Alternative model
- `session-type-checker` - Type-safe messaging
- `concurrency-verifier` - Verify correctness

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| Hoare "Communicating Sequential Processes" | CSP foundation |
| Hewitt et al. "Actor Model" | Original actor paper |
| Go language channels | Practical implementation |

## Tradeoffs and Limitations

### Approach Tradeoffs

| Approach | Pros | Cons |
|----------|------|------|
| CSP channels | Simple, composable | Manual routing |
| Actors | Scalable, location transparent | More complex |
| Publish/Subscribe | Decoupled | No reply semantics |

### When NOT to Use This Skill

- Single-threaded applications
- When shared memory is simpler
- High-frequency trading (latency)

### Limitations

- Message ordering across actors
- Distributed failures
- Backpressure handling

## Assessment Criteria

A high-quality implementation should have:

| Criterion | What to Look For |
|-----------|------------------|
| Correctness | Messages delivered |
| Fairness | No starvation |
| Performance | Scales with cores |
| Safety | No data races |

### Quality Indicators

✅ **Good**: Type-safe, handles backpressure, graceful shutdown
⚠️ **Warning**: Works but can deadlock
❌ **Bad**: Message loss, data races

## Research Tools & Artifacts

Real-world message passing systems:

| Tool | Why It Matters |
|------|----------------|
| **Akka** | Actor system for Scala/Java |
| **Erlang/OTP** | Original actor language |
| ** Orleans** | Microsoft actor framework |
| **Go channels** | CSP in Go |
| **CAF** | C++ actor framework |

### Key Systems

- **Erlang/OTP**: Production message passing
- **Akka**: JVM actor system

## Research Frontiers

Current message passing research:

| Direction | Key Papers | Challenge |
|-----------|------------|-----------|
| **Typed actors** | "Typed Actors" (2018) | Type safety |
| **Distribution** | "Distributed Actors" | Scale |
| **Failure** | "Actor Failure" | Fault tolerance |

### Hot Topics

1. **Wasm actors**: WebAssembly actors
2. **Serverless**: Functions as actors

## Implementation Pitfalls

Common message passing bugs:

| Pitfall | Real Example | Prevention |
|---------|--------------|------------|
| **Deadlock** | Cyclic waits | Avoid cycles |
| **Lost messages** | Buffer overflow | Backpressure |
| **Starvation** | Unfair scheduling | Fair queues |
