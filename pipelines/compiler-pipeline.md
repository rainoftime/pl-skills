---
name: compiler-pipeline
description: "End-to-end pipeline for building a compiler from source to native code."
version: "1.0.0"
skills:
  - lexer-generator
  - parser-generator
  - type-checker-generator
  - ssa-constructor
  - llvm-backend-generator
---

# Compiler Pipeline

This pipeline demonstrates building a compiler from source code to native executable.

## Pipeline Steps

```
Source Code → Lexer → Parser → Type Checker → SSA → LLVM IR → Native Code
```

## Step 1: Lexical Analysis

**Skill**: `lexer-generator`

**Input**: Source code as string
**Output**: Token stream

```python
# Use lexer-generator to create a lexer
source_code = """
let add = fn(x, y) { x + y };
add(1, 2)
"""

# Generated lexer produces tokens
tokens = lexer.tokenize(source_code)
# [Token(LET), Token(IDENT, "add"), Token(EQUAL), ...]
```

## Step 2: Parsing

**Skill**: `parser-generator`

**Input**: Token stream
**Output**: Abstract Syntax Tree (AST)

```python
# Use parser-generator to create a parser
ast = parser.parse(tokens)
# Program([
#   Let("add", Lambda(["x", "y"], BinOp(Var("x"), "+", Var("y")))),
#   Call(Var("add"), [Const(1), Const(2)])
# ])
```

## Step 3: Type Checking

**Skill**: `type-checker-generator`

**Input**: AST
**Output**: Typed AST or type errors

```python
# Use type-checker-generator
typed_ast = type_checker.check(ast)
# Ensures type safety before compilation
```

## Step 4: SSA Construction

**Skill**: `ssa-constructor`

**Input**: Typed AST
**Output**: SSA-form IR

```python
# Convert to SSA form
ssa_ir = ssa_constructor.convert(typed_ast)
# Each variable assigned exactly once
```

## Step 5: Code Generation

**Skill**: `llvm-backend-generator`

**Input**: SSA IR
**Output**: LLVM IR / Native code

```python
# Generate LLVM IR
llvm_ir = codegen.generate(ssa_ir)

# Compile to native
native_code = backend.compile(llvm_ir, target="x86_64")
```

## Complete Example

```python
def compile(source: str, output: str) -> bool:
    """Full compilation pipeline."""
    
    # Step 1: Lexing
    tokens = lexer.tokenize(source)
    if lexer.has_errors():
        report_errors(lexer.errors)
        return False
    
    # Step 2: Parsing
    ast = parser.parse(tokens)
    if parser.has_errors():
        report_errors(parser.errors)
        return False
    
    # Step 3: Type checking
    typed_ast = type_checker.check(ast)
    if type_checker.has_errors():
        report_errors(type_checker.errors)
        return False
    
    # Step 4: SSA construction
    ssa = ssa_constructor.convert(typed_ast)
    
    # Step 5: Optimization (optional)
    ssa = optimizer.optimize(ssa, level=2)
    
    # Step 6: Code generation
    llvm_ir = codegen.generate(ssa)
    
    # Step 7: Native compilation
    backend.compile_to_file(llvm_ir, output)
    
    return True
```

## Extensions

- Add `jit-compiler-builder` for JIT compilation
- Add `garbage-collector-implementer` for runtime
- Add `partial-evaluator` for compile-time optimization
