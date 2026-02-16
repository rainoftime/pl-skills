# Pipelines

This directory contains end-to-end workflows composed from multiple skills.

## Available Pipelines

| Pipeline | Description | Skills Used |
|----------|-------------|-------------|
| [compiler-pipeline](./compiler-pipeline.md) | Build a compiler from source to native code | lexer, parser, type-checker, SSA, LLVM |
| [verification-pipeline](./verification-pipeline.md) | Verify program correctness | dataflow, abstract interpretation, symbolic execution, Hoare logic |
| [type-system-pipeline](./type-system-pipeline.md) | Implement a complete type system | STLC, type checker, inference, subtyping |

## What is a Pipeline?

A pipeline is an end-to-end workflow that:

1. **Solves a complex problem** by composing multiple skills
2. **Reflects realistic developer workflows** from research or practice
3. **Shows how skills interact** and build on each other

## Creating a New Pipeline

To create a new pipeline:

1. Create a markdown file in this directory
2. Add frontmatter with `name`, `description`, `version`, and `skills`
3. Document each step and how skills connect
4. Provide a complete example

### Template

```markdown
---
name: my-pipeline
description: "Brief description of the pipeline."
version: "1.0.0"
skills:
  - skill-1
  - skill-2
  - skill-3
---

# Pipeline Name

Description of what this pipeline accomplishes.

## Pipeline Steps

\`\`\`
Step 1 → Step 2 → Step 3 → Output
\`\`\`

## Step 1: Name

**Skill**: `skill-name`

**Input**: ...
**Output**: ...

```python
# Example code
```

## Complete Example

```python
# Full pipeline implementation
```
```

## Contributing

Pipelines should:
- Use skills from this repository
- Reflect real-world workflows
- Include working code examples
- Be self-contained and reproducible
