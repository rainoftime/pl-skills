---
name: lexer-generator
description: 'Generates lexical analyzers from regex specifications. Use when: (1)
  Building compilers, (2) Implementing interpreters, (3) Creating domain-specific
  languages.'
version: 1.0.0
tags:
- compiler
- lexing
- parsing
- frontend
difficulty: beginner
languages:
- python
- ocaml
- rust
dependencies: []
---

# Lexer Generator

Generates lexical analyzers (tokenizers) from regex specifications.

## When to Use

- Building compilers or interpreters
- Creating lexers for DSLs
- Parsing structured text formats
- Implementing programming languages

## What This Skill Does

1. **Parses regex specs** - Converts regex to NFA/DFA
2. **Generates lexers** - Produces executable tokenizer code
3. **Handles conflicts** - Resolves longest-match ambiguities
4. **Optimizes** - Minimizes DFA states

## Key Concepts

| Concept | Description |
|---------|-------------|
| **Token** | Lexical unit (keyword, identifier, number) |
| **Lexeme** | Actual source text matched |
| **Position** | Location info for error reporting |
| **Longest match** | Prefer longest matching lexeme |
| **Priority** | First matching rule wins (tie-break) |

## Tips

- Handle unicode properly (use Unicode flag)
- Track line/column for error messages
- Skip comments and whitespace
- Handle reserved words (keyword vs identifier)
- Consider lookahead for better error recovery

## Common Issues

| Issue | Solution |
|-------|----------|
| Ambiguous patterns | Use longest match + priority |
| Performance | Use DFA, not backtracking |
| Unicode | Use `re.UNICODE` flag |
| String literals | Use greedy matching carefully |

## Related Skills

- `parser-generator` - Generate parsers
- `program-transformer` - Build ASTs
- `lambda-calculus-interpreter` - Execute programs

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| **Aho et al., "Compilers: Principles, Techniques, and Tools" (1986)** | Dragon Book; chapters 3-4 on lexical analysis |
| **Thompson, "Programming Techniques: Regular Expression Search Algorithm" (1968)** | Original NFA construction |
| **McNaughton & Yamada, "Regular Expressions and State Graphs" (1960)** | DFA construction |
| **Fischer & LeBlanc, "Crafting a Compiler" (1988)** | Practical lexer design |
| **Russ Cox, "Regular Expression Matching Can Be Simple and Fast" (2007)** | Modern regex implementation |

## Tradeoffs and Limitations

### Lexer Algorithm Tradeoffs

| Approach | Pros | Cons |
|----------|------|------|
| **Regex-based** | Easy to write | May backtrack |
| **NFA-based** | Simple construction | Large states |
| **DFA-based** | Fast matching | Large table |

### When NOT to Build a Custom Lexer

- **For simple formats**: Use existing parsers (JSON, CSV)
- **For prototyping**: String splitting may suffice
- **For existing tools**: Lex/Flex generate efficient lexers

### Complexity Considerations

- **DFA construction**: O(n²) worst case in states
- **Matching**: O(1) per character with DFA
- **NFA simulation**: O(n) per character

### Limitations

- **Ambiguity**: Keywords vs identifiers, longest match rule
- **Context sensitivity**: Can't handle indentation (use parser)
- **Unicode**: Complex character classes
- **Error recovery**: Hard to provide good error messages
- **Performance**: Backtracking regex can be exponential

## Research Tools & Artifacts

Lexer generators and tools:

| Tool | Language | What to Learn |
|------|----------|---------------|
| **Flex** | C | Fast lexer generation |
| **ANTLR lexer** | Java | Integrated lexing/parsing |
| **PLY** | Python | Lex in Python |
| **rustlex** | Rust | Safe lexer generation |
| **JFlex** | Java | Java lexer generation |

### Regex Implementations

- **RE2** (Google) - DFA-based, linear time
- **Hyperscan** (Intel) - Pattern matching
- **PCRE2** - Backtracking with optimizations

## Research Frontiers

### 1. Unicode Lexing
- **Challenge**: Character classes across scripts
- **Approach**: Unicode property classes, grapheme clusters
- **Papers**: "Unicode Support in Parsing" (various)

### 2. Incremental Lexing
- **Challenge**: Edit-based lexing for IDEs
- **Approach**: Cache tokens, re-lex only affected regions
- **Tools**: Tree-sitter (incremental)

### 3. Scannerless Parsing
- **Challenge**: Lexer/parser coupling
- **Approach**: Combine into single phase
- **Tools**: Scannerless GLR parsers

## Implementation Pitfalls

| Pitfall | Real Consequence | Solution |
|---------|-----------------|----------|
| **Longest match** | "=" vs "==" ambiguity | Use longest match |
| **Keyword vs identifier** | "if" recognized as identifier | Reserve keywords |
| **Greedy matching** | "/*/" parsed as "/*" + "/" | Careful regex |
| **Unicode** | Wrong character classes | Use Unicode properties |

### The "Keyword vs Identifier" Problem

Simple lexer issue:

```
if  -> KEYWORD
iff -> IDENTIFIER
```

Solution: Check keywords after matching identifier:

```python
def tokenize(self, source):
    match = self.longest_match(source)
    if match.type == 'IDENT' and match.text in self.keywords:
        match.type = 'KEYWORD'
    return match
```

This is why lexers need reservation!
