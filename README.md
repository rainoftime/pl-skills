<h1 align="center"><strong>✨ Skills-4-PL</strong>: Programming Languages Research Skills for LLM Agents</h1>

> A comprehensive collection of skills for Programming Languages research and development, covering POPL (theory), PLDI (implementation), and OOPSLA (systems) topics.

<p align="center">
<a href="https://platform.composio.dev/?utm_source=Github&utm_medium=Youtube&utm_campaign=2025-11&utm_content=AwesomeSkills">
  <img width="1280" height="640" alt="Composio banner" src="./banner.png">
</a>

[![Welcome Contribution](https://img.shields.io/badge/PRs-welcome-brightgreen.svg)](./CONTRIBUTING.md)
[![中文](https://img.shields.io/badge/lang-中文-red)](./README-zh.md)
[![English](https://img.shields.io/badge/lang-English-blue)](./README.md)

---

## 🌐 Skills Manager Web Interface

**[🚀 Visit Skills Manager](https://rainoftime.github.io/pl-skills/)**

Browse, search, and install skills through our interactive web interface.

---

## About This Repository

This repository contains **99 PL research skills** designed for:

- **POPL researchers** - Type systems, formal semantics, proof assistants
- **PLDI practitioners** - Compiler passes, program analysis, optimizations  
- **OOPSLA engineers** - Runtime systems, verification, concurrency
- **Graduate students** - Learning PL concepts through working implementations
- **Tool builders** - Building compilers, analyzers, and verifiers

Each skill is a **self-contained implementation** that can solve real PL research problems:
- Task-grounded (solves concrete PL problems)
- Reusable (clearly specified inputs/outputs)
- Tool-aware (operates on real code, specifications, proofs)

---

## 🎯 Skills by Conference Track

### 🔬 POPL (Theory) — Type Systems & Formal Semantics

| Skill | Description |
|-------|-------------|
| [type-checker-generator](./type-checker-generator/) | Generates type checkers from language specifications |
| [type-inference-engine](./type-inference-engine/) | Implements Hindley-Milner type inference |
| [subtyping-verifier](./subtyping-verifier/) | Verifies subtyping relations |
| [simply-typed-lambda-calculus](./simply-typed-lambda-calculus/) | STLC with products, sums, booleans |
| [dependent-type-implementer](./dependent-type-implementer/) | Dependent types (Pi, Sigma, equality) |
| [linear-type-implementer](./linear-type-implementer/) | Linear lambda calculus with resources |
| [session-type-checker](./session-type-checker/) | Session types for communication protocols |
| [ownership-type-system](./ownership-type-system/) | Ownership and borrowing (like Rust) |
| [effect-type-system](./effect-type-system/) | Effect tracking for side effects |
| [refinement-type-checker](./refinement-type-checker/) | Refinement types with predicates |
| [relational-parametricity-prover](./relational-parametricity-prover/) | Proves parametricity theorems |
| [bidirectional-type-checking](./bidirectional-type-checking/) | Bidirectional type inference/checking |
| [row-polymorphism](./row-polymorphism/) | Extensible records with row types |
| [polymorphic-effects](./polymorphic-effects/) | Effect polymorphism and handlers |
| [higher-order-abstract-syntax](./higher-order-abstract-syntax/) | HOAS for binder representation |
| [type-directed-name-resolution](./type-directed-name-resolution/) | Type-guided name disambiguation |

### 📐 POPL (Theory) — Formal Semantics

| Skill | Description |
|-------|-------------|
| [operational-semantics-definer](./operational-semantics-definer/) | Defines SOS semantics for languages |
| [denotational-semantics-builder](./denotational-semantics-builder/) | Builds denotational semantics |
| [hoare-logic-verifier](./hoare-logic-verifier/) | Verifies programs with Hoare logic |
| [separation-logician](./separation-logician/) | Separation logic for heap verification |
| [coq-proof-assistant](./coq-proof-assistant/) | Proofs in Coq (induction, tactics) |
| [bisimulation-checker](./bisimulation-checker/) | Proves bisimilarity between programs |

---

### ⚙️ PLDI (Implementation) — Compilers & Interpreters

| Skill | Description |
|-------|-------------|
| [lambda-calculus-interpreter](./lambda-calculus-interpreter/) | Untyped and simply-typed lambda calculus |
| [closure-converter](./closure-converter/) | Transforms closures to environment passing |
| [lexer-generator](./lexer-generator/) | Generates lexical analyzers |
| [parser-generator](./parser-generator/) | Generates LALR/recursive descent parsers |
| [ssa-constructor](./ssa-constructor/) | Builds Static Single Assignment form |
| [jit-compiler-builder](./jit-compiler-builder/) | JIT compilation infrastructure |
| [typed-assembly-language](./typed-assembly-language/) | Typed assembly language verifier |
| [cps-transformer](./cps-transformer/) | Continuation-passing style transform |
| [partial-evaluator](./partial-evaluator/) | Program specialization via PE |
| [defunctionalization](./defunctionalization/) | Closure elimination to data types |
| [multi-stage-programming](./multi-stage-programming/) | Staged compilation and code gen |
| [dsl-embedding](./dsl-embedding/) | Embedding DSLs in host languages |

### 📊 PLDI (Implementation) — Program Analysis

| Skill | Description |
|-------|-------------|
| [dataflow-analysis-framework](./dataflow-analysis-framework/) | General dataflow analysis framework |
| [abstract-interpretation-engine](./abstract-interpretation-engine/) | Abstract interpretation engine |
| [alias-and-points-to-analysis](./alias-and-points-to-analysis/) | Points-to and alias analysis |
| [taint-analysis](./taint-analysis/) | Taint tracking for security |
| [model-checker](./model-checker/) | Finite-state model checking |

---

### ⚡ OOPSLA (Systems) — Runtime & Optimization

| Skill | Description |
|-------|-------------|
| [garbage-collector-implementer](./garbage-collector-implementer/) | GC (mark-compact, generational) |
| [constant-propagation-pass](./constant-propagation-pass/) | Dataflow constant propagation |
| [common-subexpression-eliminator](./common-subexpression-eliminator/) | CSE optimization pass |
| [incremental-computation](./incremental-computation/) | Change propagation and adaptivity |

### 🔒 OOPSLA (Systems) — Verification

| Skill | Description |
|-------|-------------|
| [symbolic-execution-engine](./symbolic-execution-engine/) | Symbolic execution engine |
| [invariant-generator](./invariant-generator/) | Infers loop invariants |
| [loop-termination-prover](./loop-termination-prover/) | Proves loop termination |
| [weak-memory-model-verifier](./weak-memory-model-verifier/) | Verifies weak memory behaviors |

### 🔀 OOPSLA (Systems) — Concurrency

| Skill | Description |
|-------|-------------|
| [actor-model-implementer](./actor-model-implementer/) | Actor concurrency model |
| [software-transactional-memory](./software-transactional-memory/) | STM implementation |
| [race-detection-tool](./race-detection-tool/) | Dynamic race detection |

---

## 📖 Usage

Each skill is packaged as a folder containing a `SKILL.md` file.

### Install a Skill

```bash
# Copy the skill folder to your skills directory
cp -r skill-folder ~/.claude/skills
```

### Using a Skill

Skills are automatically triggered based on user requests matching the skill description. You can also explicitly invoke a skill:

> Using "type-checker-generator" to generate a type checker for my language

---

## 🤝 Contributing

We welcome contributions from:
- **PL researchers** (new skills for type systems, semantics, verification)
- **Compiler developers** (optimization passes, analysis frameworks)
- **Formal methods practitioners** (proof assistants, model checkers)

Please read [Contributing Guidelines](CONTRIBUTING.md) before submitting.

---

## 📚 Reference

Skills inspired by:
- [awesome-claude-skills](https://github.com/ComposioHQ/awesome-claude-skills/)
- [anthropics-skills](https://github.com/anthropics/skills/)

---

## 🔄 Pipelines

End-to-end workflows composed from multiple skills:

| Pipeline | Description |
|----------|-------------|
| [compiler-pipeline](./pipelines/compiler-pipeline.md) | Build a compiler from source to native code |
| [verification-pipeline](./pipelines/verification-pipeline.md) | Verify program correctness |
| [type-system-pipeline](./pipelines/type-system-pipeline.md) | Implement a complete type system |

See [pipelines/](./pipelines/) for more details.