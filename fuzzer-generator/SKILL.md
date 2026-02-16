---
name: fuzzer-generator
description: "Creates fuzzing tools that generate random inputs to find bugs and security vulnerabilities."
version: "1.0.0"
tags: [fuzzing, security, testing, bug-finding, random-generation]
difficulty: intermediate
languages: [python, rust, c, go]
dependencies: [property-based-tester, taint-analysis]
---

# Fuzzer Generator

Creates fuzzing tools that automatically generate random inputs to discover bugs, crashes, and security vulnerabilities in programs.

## When to Use This Skill

- Finding crashes and memory safety issues
- Discovering input validation bugs
- Security vulnerability discovery
- Compiler bug finding

## What This Skill Does

1. **Input Generation**: Creates random valid inputs for target programs
2. **Coverage Tracking**: Monitors code coverage to guide fuzzing
3. **Mutation Strategies**: Implements mutation and generation-based fuzzing
4. **Crash Analysis**: Triages and minimizes crashing inputs

## Key Concepts

| Concept | Description |
|---------|-------------|
| Coverage-guided fuzzing | Uses coverage to prioritize inputs |
| Corpus | Set of interesting inputs |
| Mutation | Small changes to existing inputs |
| Crash minimization | Reducing inputs to minimal forms |

## Tips

- Build with AddressSanitizer for memory safety bugs
- Use libFuzzer for C/C++, Atheris for Python
- Maintain corpus of interesting inputs
- Minimize crashes to find root causes

## Related Skills

- `property-based-tester` - Structured property testing
- `taint-analysis` - Track untrusted input
- `sandbox-builder` - Safe fuzzing environment

## Canonical References

| Reference | Why It Matters |
|-----------|----------------|
| libFuzzer: in-process coverage-guided fuzzing | LLVM fuzzing engine |
| AFL: American Fuzzy Lop | Popular greybox fuzzer |
| Finding Bugs in JavaScript Engines | Fuzzing case study |

## Tradeoffs and Limitations

| Approach | Pros | Cons |
|----------|------|------|
| Coverage-guided | Efficient, finds deep bugs | Requires instrumentation |
| Blackbox | No source needed | Less effective |
| Grammar-based | Generates valid inputs | Requires grammar |

## Assessment Criteria

| Criterion | What to Look For |
|-----------|------------------|
| Coverage | Efficient code coverage |
| Bug finding | Discovers real bugs |
| Performance | High tests/second |

### Quality Indicators

✅ **Good**: Good coverage, finds bugs, high throughput
⚠️ **Warning**: Limited coverage, slow
❌ **Bad**: No bugs found, crashes

## Research Tools & Artifacts

Fuzzing tools and frameworks:

| Tool | Language | What to Learn |
|------|----------|---------------|
| **libFuzzer** | C/C++ | In-process coverage-guided |
| **AFL++** | C | Greybox fuzzing |
| **Honggfuzz** | C | Feedback-driven |
| **Fuzzilli** | JavaScript | JavaScript engine fuzzing |
| **Oathbreaker** | Python | Grammar-based |

### Fuzzing Infrastructure

- **OSS-Fuzz** - Continuous fuzzing service
- **Fuzzbench** - Fuzzer evaluation framework

## Research Frontiers

### 1. Fuzzing with LLMs
- **Approach**: Use language models for input generation
- **Papers**: "Fuzzing with LLMs" (2023+)
- **Tools**: ChatGPT-assisted fuzzing

### 2. Hybrid Fuzzing
- **Approach**: Combine symbolic execution with fuzzing
- **Papers**: "Driller" (Shoshitaishvili)
- **Tools**: QSYM, Angora

## Implementation Pitfalls

| Pitfall | Real Consequence | Solution |
|---------|-----------------|----------|
| **Coverage plateau** | Stops finding new paths | Add corpus, mutations |
| **Crash duplication** | Too many similar crashes | Minimize inputs |
