# Contributing to Skills-4-SE

Thank you for your interest in contributing!  
This repository aims to build a **high-quality, lifecycle-aware Skill library** for LLM-powered software engineering systems.

We welcome contributions from both:
- **Researchers** (new Skills, evaluation protocols, case studies)
- **Practitioners** (real-world workflows, pipelines, tooling)

To keep the repository useful, reproducible, and maintainable, we follow the guidelines below.

## Before You Start

- Ensure your skill is based on a **real use case**, not a hypothetical scenario.
- Search existing skills to avoid duplicates.
- If possible, attribute the use case to the original person or source.

## Skill Requirements

All skills must:

1. **Solve a real problem** - Based on actual usage, not theoretical applications.
2. **Be well-documented** - Include clear instructions, examples, and use cases.
3. **Be accessible** - Written for non-technical users when possible.
4. **Include examples** - Show practical, real-world usage.
5. **Be tested** - Verify the skill works across Claude.ai, Claude Code, and/or API.
6. **Be safe** - Confirm before destructive operations.
7. **Be portable** - Work across Claude platforms when applicable.


## Skill Structure
Create a new folder with your skill name (use lowercase and hyphens):

```
skill-name/
├── SKILL.md  (See [template skill](template/SKILL.md))
├── references/ (optional)
├── scripts/ (optional)
└── assets/ (optional)
```

### SKILL.md Template

Use the template at [template/SKILL.md](template/SKILL.md) for your skill.

Required frontmatter fields:
- `name`: Skill identifier (lowercase, hyphens)
- `description`: One-sentence description

Optional but recommended frontmatter fields:
- `version`: Skill version (default: "1.0.0")
- `tags`: Array of relevant tags
- `difficulty`: beginner | intermediate | advanced
- `languages`: Array of programming languages used
- `dependencies`: Array of related skill names

### Adding Your Skill to README
- Choose the appropriate category
- Add your skill within the category

```
- [Skill Name](./skill-name/) - One-sentence description. (Inspired by [Person/Source])
```

- Follow the existing format, no emojis in the skill name.


## Pull Request Process
- Fork the repository
- Create a branch: `git checkout -b add-skill-name`
- Add your skill folder with SKILL.md
- Update README.md with your skill in the appropriate category
- Commit your changes: `git commit -m "Add [Skill Name] skill"`
- Push to your fork: `git push origin add-skill-name`
- Open a Pull Request

## Pull Request Guidelines
Your PR should:

- Title: "Add [Skill Name] skill"
- Description: Explain the real-world use case and include:
   - What problem it solves
   - In which scenario
   - Applicable scope (programming language, input/output constraints)
   - Attribution/inspiration source (optional)


## 📌 What Can Be Contributed?

### 1. New Skills
A Skill represents a **reusable software engineering capability** (not a one-off prompt).

Good Skill candidates:
- Solve a **well-defined software engineering task**
- Operate on real artifacts (code, tests, specs, configs, logs)
- Can be reused across projects or contexts

Examples:
- Assertion synthesis for unit tests
- Ambiguity detection in natural-language requirements
- Formal specification inference from code
- CI configuration misuse detection

---

### 2. Skill Improvements
You may contribute by:
- Improving existing instructions
- Adding better examples
- Documenting failure modes
- Extending evaluation criteria

---

### 3. Pipelines
Pipelines demonstrate **end-to-end workflows** composed from multiple Skills.

Examples:
- Bug report → reproducing test → patch
- Spec → code → verification
- Failing CI → diagnosis → fix

Pipelines should reflect **realistic developer workflows**. A demonstration of how a proposed pipeline

---

### 4. Evaluation & Benchmarks
We strongly encourage contributions that improve **rigor and evaluation**, including:
- Skill-level evaluation protocols
- Case studies on real projects
- Failure analysis and ablation studies

---


## 🤝 Code of Conduct

We expect all contributors to:
- Be respectful and constructive
- Focus discussions on technical content
- Welcome feedback and iteration

This repository follows a **collaborative and research-friendly culture**.


## 💬 Questions & Discussions

If you are unsure whether your idea fits, feel free to:
- Open an issue to discuss a proposed Skill
- Ask for feedback before implementing

We appreciate your interest in helping build a shared Skill layer for software engineering.


## Acknowledge
- [How to create custom skills](https://support.claude.com/en/articles/12512198-how-to-create-custom-skills)
- [awesome-claude-skills](https://github.com/ComposioHQ/awesome-claude-skills/)