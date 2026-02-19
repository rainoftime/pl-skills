---
name: parser-generator
description: 'Generates LALR(1) and recursive-descent parsers from grammar specifications.
  Use when: (1) Building compilers, (2) Creating DSLs, (3) Parsing configuration files.'
version: 1.0.0
tags:
- compiler
- parsing
- grammars
- frontend
difficulty: intermediate
languages:
- python
- ocaml
- rust
dependencies:
- lexer-generator
---

# Parser Generator

Generates parsers from context-free grammar specifications.

## When to Use

- Building compilers for new languages
- Creating DSL parsers
- Parsing structured text/data formats
- Generating ASTs from source code

## What This Skill Does

1. **Parses grammar specs** - Converts BNF to internal representation
2. **Generates parsers** - LALR(1) or recursive descent
3. **Handles ambiguity** - Resolves with precedence/associativity
4. **Reports errors** - Generates meaningful error messages

## Key Concepts
    
    def peek(self, type: str) -> bool:
        """Check if current token has type"""
        return self.current().type == type
    
    # Grammar rules
    
    def parse_expr(self):
        """Expr -> Term (('+' | '-') Term)*"""
        result = self.parse_term()
        
        while self.peek("PLUS") or self.peek("MINUS"):
            op = self.consume().value
            right = self.parse_term()
            result = BinOp(op, result, right)
        
        return result
    
    def parse_term(self):
        """Term -> Factor (('*' | '/') Factor)*"""
        result = self.parse_factor()
        
        while self.peek("TIMES") or self.peek("DIV"):
            op = self.consume().value
            right = self.parse_factor()
            result = BinOp(op, result, right)
        
        return result
    
    def parse_factor(self):
        """Factor -> NUMBER | '(' Expr ')'"""
        if self.peek("NUMBER"):
            return Number(int(self.consume().value))
        
        if self.peek("LPAREN"):
            self.consume()
            result = self.parse_expr()
            self.consume("RPAREN")
            return result
        
        raise ParseError(f"Unexpected token: {self.current()}")
```

### AST Nodes

```python
@dataclass
class ASTNode:
    """Base class for AST nodes"""
    pass

@dataclass
class Number(ASTNode):
    value: int

@dataclass
class BinOp(ASTNode):
    op: str
    left: ASTNode
    right: ASTNode

@dataclass
class UnaryOp(ASTNode):
    op: str
    operand: ASTNode

@dataclass
class Var(ASTNode):
    name: str

@dataclass
class Assign(ASTNode):
    name: str
    value: ASTNode

@dataclass
class If(ASTNode):
    condition: ASTNode
    then_branch: ASTNode
    else_branch: Optional[ASTNode]

@dataclass
class While(ASTNode):
    condition: ASTNode
    body: ASTNode

@dataclass
class Block(ASTNode):
    statements: list[ASTNode]
```

### LALR(1) Parser Generator

```python
# Simplified LALR(1) parser generator
from collections import defaultdict

class Grammar:
    def __init__(self):
        self.productions = []  # [(lhs, [rhs symbols])]
        self.terminals = set()
        self.nonterminals = set()
        self.start = None
    
    def add_production(self, lhs, rhs):
        """Add production: lhs -> rhs"""
        self.productions.append((lhs, rhs))
        self.nonterminals.add(lhs)
        for sym in rhs:
            if sym.islower() or sym in ('+', '*', '(', ')'):
                self.terminals.add(sym)
            else:
                self.nonterminals.add(sym)
    
    def augmented_start(self):
        """Create augmented grammar with S' -> S"""
        self.start = self.productions[0][0]
        self.productions.insert(0, ("S'", [self.start]))
        self.nonterminals.add("S'")

# Item: production with dot position
@dataclass
class LRItem:
    lhs: str
    rhs: tuple
    dot: int  # position in rhs
    lookaheads: set

def closure(items, grammar):
    """Compute closure of LR(1) items"""
    closure_set = set(items)
    changed = True
    
    while changed:
        changed = False
        for item in list(closure_set):
            if item.dot < len(item.rhs):
                symbol = item.rhs[item.dot]
                if symbol in grammar.nonterminals:
                    # Find all productions for this nonterminal
                    for lhs, rhs in grammar.productions:
                        if lhs == symbol:
                            # Calculate lookahead
                            beta = item.rhs[item.dot + 1:]
                            new_lookaheads = compute_lookahead(
                                item.lookaheads, beta, grammar
                            )
                            new_item = LRItem(lhs, rhs, 0, new_lookaheads)
                            if new_item not in closure_set:
                                closure_set.add(new_item)
                                changed = True
    
    return closure_set

def compute_lookahead(lookaheads, beta, grammar):
    """Compute lookahead for GOTO"""
    result = set(lookaheads)
    for symbol in beta:
        if symbol in grammar.terminals:
            return {symbol}
        # Handle nullable nonterminals
        if is_nullable(symbol, grammar):
            continue
        break
    return result

def goto(items, symbol, grammar):
    """Compute GOTO(I, X)"""
    goto_set = set()
    for item in items:
        if item.dot < len(item.rhs) and item.rhs[item.dot] == symbol:
            new_item = LRItem(
                item.lhs, 
                item.rhs, 
                item.dot + 1, 
                item.lookaheads
            )
            goto_set.add(new_item)
    return closure(goto_set, grammar)

def build_lalr_table(grammar):
    """Build LALR(1) parsing table"""
    grammar.augmented_start()
    
    # Build canonical collections
    C = [closure({LRItem("S'", (grammar.start,), 0, {"$"})}, grammar)]
    
    # ... (complete algorithm in production code)
    
    # Build action/goto tables
    action = {}
    goto_table = {}
    
    # ... fill in tables
    
    return action, goto_table
```

### Using the LALR Parser

```python
def lalr_parse(tokens, grammar):
    """LALR(1) parser"""
    action, goto = build_lalr_table(grammar)
    
    stack = [0]  # State stack
    symbols = []  # Symbol stack
    
    while True:
        state = stack[-1]
        token = tokens[lookahead]
        
        if (state, token.type) in action:
            action_entry = action[(state, token.type)]
            
            if action_entry[0] == 'shift':
                stack.append(action_entry[1])
                symbols.append(token)
                lookahead += 1
            
            elif action_entry[0] == 'reduce':
                prod = action_entry[1]
                lhs, rhs = grammar.productions[prod]
                # Pop len(rhs) states and symbols
                for _ in range(len(rhs)):
                    stack.pop()
                    symbols.pop()
                # Push nonterminal
                symbols.append(lhs)
                # New state
                new_state = goto[stack[-1], lhs]
                stack.append(new_state)
            
            elif action_entry[0] == 'accept':
                return symbols[1]  # Return AST
            
            else:
                raise ParseError(f"Unknown action: {action_entry}")
        else:
            raise ParseError(f"Unexpected token: {token}")
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| **Terminal** | Token from lexer (NUMBER, IDENT) |
| **Nonterminal** | Grammar symbol (Expr, Stmt) |
| **Production** | Rule defining nonterminal |
| **LR(0) item** | Production with dot position |
| **Lookahead** | Token to decide action |
| **Conflict** | Shift/reduce or reduce/reduce ambiguity |

## Precedence & Associativity

```python
# Specify in grammar
precedence = [
    ('left', ['PLUS', 'MINUS']),
    ('left', ['TIMES', 'DIV']),
    ('right', ['UMINUS']),  # Unary minus
]

# Resolve during parser generation
# 1. Shift > Reduce for unambiguous precedence
# 2. Left-assoc: reduce on leftmost match
# 3. Right-assoc: reduce on rightmost match
```

## Tips

- Start with simple grammars, add features incrementally
- Use left-recursion for recursive descent (or convert to right)
- Handle errors gracefully (error productions, recovery)
- Track source locations in AST
- Consider semantic actions during parsing

## Common Issues

| Issue | Solution |
|-------|----------|
| Left recursion | Transform to right recursion |
| Ambiguity | Use precedence/associativity |
| Infinite loop | Check for ε-productions |
| Poor errors | Add error productions |

## Tradeoffs and Limitations

### Algorithm Tradeoffs

| Approach | Pros | Cons |
|----------|------|------|
| **Recursive Descent** | Simple, intuitive, good errors | Left recursion problems, backtracking |
| **LL(1)** | Predictable, no backtrack | Limited expressiveness |
| **LR(1)/LALR** | Most powerful, deterministic | Complex table generation |
| **GLR** | Handles ambiguity | Complex, harder error messages |

### When NOT to Use This Approach

- **For highly ambiguous grammars**: Consider parsing expression grammars (PEGs) or GLR
- **For streaming/large inputs**: Consider incremental parsing
- **For error recovery**: Use error productions and recovery strategies

### Limitations

- **LL/LR limits**: Not all context-free grammars are parsable
- **Ambiguity**: Some grammars are inherently ambiguous; must resolve
- **Error messages**: Parser errors can be cryptic; requires effort for good UX
- **Left recursion**: Traditional recursive descent fails; requires transformation

## Assessment Criteria

A high-quality parser generator should have:

| Criterion | What to Look For |
|-----------|------------------|
| **Coverage** | Handles full grammar (not just subset) |
| **Error recovery** | Can continue after errors |
| **Error messages** | Clear, shows location |
| **AST quality** | Preserves source info |
| **Performance** | Linear time parsing |
| **Ambiguity** | Resolves conflicts correctly |

### Quality Indicators

✅ **Good**: Complete grammar coverage, good error messages, preserves locations
⚠️ **Warning**: Limited grammar coverage, poor error messages
❌ **Bad**: Wrong parses accepted, crashes on valid input

## Related Skills

- `lexer-generator` - Generate lexers
- `program-transformer` - Transform ASTs
- `lambda-calculus-interpreter` - Execute ASTs

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| **Aho, Lam, Sethi, Ullman, "Compilers: Principles, Techniques, and Tools" (Dragon Book)** | Chapters 4-5 on parsing; LR parsing theory |
| **Grune & Jacobs, "Parsing Techniques: A Practical Guide"** | Comprehensive survey of parsing algorithms |
| **Knuth, "On the Translation of Context-Free Grammars"** | Original LR(k) paper |
| **DeRemer, "Simple LR(k) Grammars" (1971)** | LALR paper |
| **Norvell, "Introduction to Parsing"** | Excellent tutorial on LR parsing |

## Research Tools & Artifacts

Real-world parser generators and tools:

| Tool | Language | What to Learn |
|------|----------|---------------|
| **ANTLR 4** | Java | ALL(*) parsing, semantic predicates |
| **Menhir** | OCaml | LR(1), incremental, error messages |
| **Yacc/Bison** | C | Classic LALR, battle-tested |
| **Happy** | Haskell | LALR(1), with optional GLR extension |
| **Lalrpop** | Rust | Rust integration, error recovery |
| **pest** | Rust | PEG parsing, grammar derivation |

### Parser Generator Research

- **GLR (Generalized LR)** - Handles ambiguity gracefully
- **Incremental Parsing** - Reparse after small edits
- **Error Recovery** - Parse errors, continue, report
- **Packrat Parsing** - PEG with memoization

## Research Frontiers

### 1. Adaptive Parsing
- **Approach**: Choose parser strategy based on input
- **Papers**: "Adaptive LL(*) Parsing" (Parr & Fisher)
- **Tool**: ANTLR 4's ALL(*) algorithm
- **Advantage**: Handles more grammars

### 2. Incremental Parsing
- **Approach**: Reuse parse tree after edits
- **Papers**: "Incremental Parsing" (Wagner & Graham)
- **Tools**: Roslyn (C#), tree-sitter
- **Advantage**: Fast for IDEs

### 3. Error Recovery Strategies
- **Approach**: Recover from errors, continue parsing
- **Papers**: "Error Recovery in LR Parsers" (Burke & Fisher)
- **Techniques**: Panic mode, phrase-level, partial parsing
- **Advantage**: Better error messages

### 4. PEGs vs CFGs
- **PEG**: Parsing Expression Grammars (ordered choice)
- **CFG**: Context-free grammars (ambiguous)
- **Papers**: "Parsing Expression Grammars" (Ford)
- **Tools**: PEG.js, pest, Scala parser combinators

## Implementation Pitfalls

| Pitfall | Real Consequence | Solution |
|---------|-----------------|----------|
| **Left recursion** | Infinite loop in recursive descent | Convert to right recursion or use packrat |
| **Ambiguity** | Unexpected parses | Use precedence, GLR |
| **Epsilon loops** | Parser hangs | Fix-point detection |
| **Wrong precedence** | "shift/reduce conflict" | Declare precedence correctly |
| **Missing error recovery** | Single error stops parse | Add error productions |

### The "Dangling Else" Problem

Classic ambiguity in grammars:

```
stmt → if expr then stmt
      | if expr then stmt else stmt
      | ...

if E1 then if E2 then S1 else S2
-- Which if does else bind to?
-- Standard: binds to innermost (shift-reduce conflict)
```

### LR Conflict Resolution

```yacc
%left '+' '-'
%left '*' '/'
%right '='  /* Lowest precedence */

/* In expr:  expr: expr '+' expr  %prec '+'  */
/* Use %prec to assign precedence to rules */
```

This is why bison uses precedence declarations!
```
