---
name: rust-borrow-checker
description: 'Implements Rust-style ownership and borrowing verification. Use when:
  (1) Building memory-safe languages, (2) Implementing borrow checking, (3) Creating
  safe systems languages.'
version: 1.0.0
tags:
- type-systems
- borrow-checker
- ownership
- rust
difficulty: advanced
languages:
- rust
dependencies:
- ownership-type-system
---

# Rust Borrow Checker

Implements Rust-style ownership, borrowing, and lifetime verification.

## When to Use

- Building memory-safe languages
- Implementing borrow checking
- Creating safe systems languages
- Verifying data race freedom
- Implementing affine/linear types

## What This Skill Does

1. **Tracks ownership** - Each value has single owner
2. **Enforces borrowing** - Mutable/immutable references
3. **Verifies lifetimes** - Reference validity
4. **Detects data races** - At compile time

## Key Concepts

| Concept | Description |
|---------|-------------|
| **Ownership** | Each value has single owner |
| **Borrow** | Reference to owned value |
| **Lifetime** | Duration reference is valid |
| **Region** | Scope where reference valid |
| **Move** | Transfer ownership |

## Borrow Rules

| Rule | Description |
|------|-------------|
| **One mutable** | Only one mutable borrow OR many immutable |
| **No dangling** | References must not outlive referent |
| **Move vs copy** | Copy for Copy types, move otherwise |
| **Drop order** | Borrows must be released before drop |

## Tips

- Start with owned values, add borrowing
- Implement NLL (non-lexical lifetimes) for better UX
- Use lifetime elision rules for ergonomics
- Consider async/await lifetime interactions
- Handle unsafe blocks with care

## Related Skills

- `ownership-type-system` - Basic ownership types
- `linear-type-implementer` - Linear types (generalization)
- `race-detection-tool` - Dynamic race detection
- `separation-logician` - Memory safety proofs

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| **Matsakis & Klock, "The Rust Language: Memory Model and Lifetime System" (2014)** | Original Rust ownership and borrowing design |
| **Rust Reference, Chapter 4: "Lifetimes and Borrowing"** | Official lifetime and borrow specification |
| **N. Matsakis, "A Primer on Rust Lifetimes" (blog series, 2014-2016)** | Deep dives on borrow checker design decisions |
| **N. Matsakis & R. Klock, "The Rust Borrow Checker" (Rust Belt Rust 2016)** | Overview of borrow checker implementation |

## Tradeoffs and Limitations

### Design Choices

| Approach | Pros | Cons |
|----------|------|------|
| **Lexical lifetimes** | Simple | Less precise |
| **NLL** | Better errors | Complex |
| **Polonius** | Most precise | Slow |

### Limitations

- Learning curve for users
- Some valid programs rejected (escape analysis)
- Unsafe code circumvents guarantees
- Complex interactions with async
- Borrow checker is complex to implement

## Research Tools & Artifacts

Rust borrow checker implementations:

| Tool | What to Learn |
|------|---------------|
| **rustc borrow checker** | Production implementation |
| **Polonius** | NLL algorithm |
| **Oxide** | Reference implementation |

### Key Papers

- **Matsakis & Klock** - Rust design papers
- **NLL papers** - Non-lexical lifetimes

## Research Frontiers

### 1. Polonius
- **Goal**: More precise borrow checking
- **Approach**: Move errors as dataflow facts
- **Papers**: "Polonius: A New Borrow Checker" (Jung et al., 2018)
- **Status**: Experimental in rustc

### 2. Async/await and Lifetimes
- **Goal**: Better lifetime handling in async code
- **Approach**: Extended lifetime rules for generators
- **Papers**: "Rust RFC 2394: async/await"

### 3. Formal Verification of Rust
- **Goal**: Prove memory safety formally
- **Approach**: RustBelt, semantic type system
- **Papers**: Jung et al. "RustBelt: Securing Rust" (POPL 2018)

## Implementation Pitfalls

| Pitfall | Real Consequence | Solution |
|---------|-----------------|----------|
| **NLL complexity** | Wrong error messages | Careful dataflow algorithm |
| **Lifetime inference** | Overly conservative | Better region inference |
| **Async interactions** | Rejected valid code | Extend lifetime rules |
| **Unsafe escape hatch** | Lost guarantees | Clear unsafe boundaries |
