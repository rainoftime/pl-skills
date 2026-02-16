---
name: skill-name
description: "One-sentence description of what this skill does and when to use it."
version: "1.0.0"
tags: [tag1, tag2, tag3]
difficulty: beginner
languages: [python, ocaml, coq, rust, haskell]
dependencies: []

# Actionable triggers - phrases that activate this skill
triggers:
  - "implement a lambda calculus interpreter"
  - "build an interpreter for functional language"
  - "understand call-by-value vs call-by-name"

# Ready-to-use prompts
action_prompts:
  - "Implement a call-by-value interpreter for untyped lambda calculus in Python"
  - "Add call-by-name evaluation strategy to my lambda calculus interpreter"
  - "Explain the difference between closures and open terms"

# Optional slash commands
commands: []

# Optional script file (e.g., run.py, main.rs)
script: null
---

# Skill Name

> **Status**: Ready to use | **Auto-trigger**: Yes

## Triggers

This skill activates when user mentions:
- Implementing lambda calculus interpreters
- Understanding evaluation strategies (CBV, CBN)
- Building functional language interpreters

## Action Prompts

Use these prompts directly:

```
Implement a call-by-value lambda calculus interpreter with:
- Var, Abs, App AST nodes
- Closure environment
- Beta reduction
```

```
Add call-by-name evaluation to existing interpreter:
- Thunk implementation
- Lazy argument evaluation
- Compare with call-by-value behavior
```

## When to Use This Skill

- Bullet point use case 1
- Bullet point use case 2
- Bullet point use case 3

## What This Skill Does

1. **Capability 1**: Description
2. **Capability 2**: Description
3. **Capability 3**: Description

## How to Use

### Basic Usage

```language
# Simple example code
```

### Using the Script

```bash
# If script is provided:
python run.py --input "lambda x. x"
python run.py --strategy cbv --file example.lc
```

### Advanced Usage

```language
# More complex example with options
```

## Test Cases

| Input | Expected Output | Description |
|-------|----------------|-------------|
| `(λx. x) (λy. y)` | `λy. y` | Identity application |
| `(λx. λy. x) (λz. z)` | `λy. λz. z` | Constant function |
| `((λf. f f) (λx. x))` | `λx. x` | Omega combinator |

## Key Concepts

| Concept | Description |
|---------|-------------|
| Concept 1 | Description 1 |
| Concept 2 | Description 2 |

## Tips

- Tip 1
- Tip 2
- Tip 3

## Common Use Cases

- Use case 1
- Use case 2
- Use case 3

## Related Skills

- `skill-name` - Brief description

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| Reference 1 | Description |
| Reference 2 | Description |

## Tradeoffs and Limitations

### Approach Tradeoffs

| Approach | Pros | Cons |
|----------|------|------|
| Approach 1 | Pros 1 | Cons 1 |
| Approach 2 | Pros 2 | Cons 2 |

### When NOT to Use This Skill

- Scenario 1
- Scenario 2

### Limitations

- Limitation 1
- Limitation 2

## Assessment Criteria

A high-quality implementation should have:

| Criterion | What to Look For |
|-----------|------------------|
| Criterion 1 | Description 1 |
| Criterion 2 | Description 2 |

### Quality Indicators

✅ **Good**: Description of good implementation
⚠️ **Warning**: Description of warning signs
❌ **Bad**: Description of bad implementation
