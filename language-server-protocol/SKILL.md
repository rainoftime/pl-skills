---
name: language-server-protocol
description: "Implements LSP servers for IDE features like go-to-definition, hover, and refactoring."
version: "1.0.0"
tags: [ide, tooling, language-server, editor-integration]
difficulty: intermediate
languages: [python, typescript, rust, go]
dependencies: [type-inference-engine, parser-generator]
---

# Language Server Protocol

Implements Language Server Protocol (LSP) servers that provide IDE features: autocomplete, go-to-definition, hover documentation, refactoring, and more.

## When to Use This Skill

- Building IDE support for programming languages
- Adding language features to editors (VS Code, Emacs, Vim)
- Implementing code navigation and refactoring
- Creating language-aware tools

## What This Skill Does

1. **LSP Server**: Implements JSON-RPC based LSP protocol
2. **Text Documents**: Manages source files with sync
3. **Code Intelligence**: Provides hover, completion, definitions
4. **Refactorings**: Implements code actions and rename

## Key Concepts

| Concept | Description |
|---------|-------------|
| Text Document Sync | Managing document state |
| Request/Notification | LSP message types |
| Location | URI + Range for code positions |
| Code Action | Edit + Command for refactoring |

## Tips

- Implement incremental sync for large files
- Use AST indexing for fast symbol lookup
- Cache expensive computations
- Handle concurrent document changes

## Related Skills

- `parser-generator` - Parse source code
- `type-inference-engine` - Type information for hover
- `abstract-interpretation-engine` - Static analysis

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| LSP Specification | Official protocol docs |
| VS Code Extensions | Language server examples |
| Tree-sitter | Incremental parsing for LSP |

## Tradeoffs and Limitations

| Approach | Pros | Cons |
|----------|------|------|
| Full index | Accurate, fast nav | Slow startup |
| On-demand | Fast startup | Slower nav |
| Local cache | Works offline | Sync complexity |

## Assessment Criteria

| Criterion | What to Look For |
|-----------|------------------|
| Protocol compliance | Passes LSP test suite |
| Responsiveness | Fast response times |
| Completeness | All key features |

### Quality Indicators

✅ **Good**: Protocol compliant, responsive, complete
⚠️ **Warning**: Some features missing, slow
❌ **Bad**: Protocol errors, crashes

## Research Tools & Artifacts

Real-world LSP implementations:

| Tool | Why It Matters |
|------|----------------|
| **clangd** | C/C++ LSP server |
| **rust-analyzer** | Rust LSP server |
| **pylsp** | Python LSP server |
| **gopls** | Go LSP server |
| **typescript-language-server** | TypeScript LSP |

### Key Servers

- **rust-analyzer**: Fast Rust IDE support
- **clangd**: C/C++ with clang

## Research Frontiers

Current LSP research:

| Direction | Key Papers | Challenge |
|-----------|------------|-----------|
| **Performance** | "Fast LSP" | Latency |
| **Incremental** | "Incremental Analysis" | Change impact |
| **Remote** | "Remote LSP" | Distributed |

### Hot Topics

1. **Language server for new langs**: Building LSP for new languages
2. **WASM LSP**: Running LSP in browser

## Implementation Pitfalls

Common LSP bugs:

| Pitfall | Real Example | Prevention |
|---------|--------------|------------|
| **Slow** | Blocked responses | Async processing |
| **Memory** | Large projects | Incremental |
| **Sync** | Stale results | Proper invalidation |
