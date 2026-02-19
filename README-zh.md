<h1 align="center"><strong>✨ Skills-4-PL</strong>：面向 LLM 智能体的编程语言研究技能</h1>

> 面向编程语言研究与开发的综合技能集合。

<p align="center">
<a href="https://platform.composio.dev/?utm_source=Github&utm_medium=Youtube&utm_campaign=2025-11&utm_content=AwesomeSkills">
  <img width="1280" height="640" alt="Skills-4-PL banner" src="./banner.svg">
</a>

[![欢迎贡献](https://img.shields.io/badge/PRs-welcome-brightgreen.svg)](./CONTRIBUTING.md)
[![中文](https://img.shields.io/badge/lang-中文-red)](./README-zh.md)
[![English](https://img.shields.io/badge/lang-English-blue)](./README.md)

---

## ⚠️ 验证状态

这些技能由 LLM 生成，可能包含**幻觉、事实错误或不正确的引用**。人工验证正在进行中。

| 技能 | 状态 | 验证者 |
|-------|--------|-------------|
| type-checker-generator | ❌ 未验证 | |
| type-inference-engine | ❌ 未验证 | |
| subtyping-verifier | ❌ 未验证 | |
| simply-typed-lambda-calculus | ❌ 未验证 | |
| dependent-type-implementer | ❌ 未验证 | |
| linear-type-implementer | ❌ 未验证 | |
| session-type-checker | ❌ 未验证 | |
| ownership-type-system | ❌ 未验证 | |
| effect-type-system | ❌ 未验证 | |
| refinement-type-checker | ❌ 未验证 | |
| relational-parametricity-prover | ❌ 未验证 | |
| bidirectional-type-checking | ❌ 未验证 | |
| row-polymorphism | ❌ 未验证 | |
| polymorphic-effects | ❌ 未验证 | |
| higher-order-abstract-syntax | ❌ 未验证 | |
| type-directed-name-resolution | ❌ 未验证 | |
| operational-semantics-definer | ❌ 未验证 | |
| denotational-semantics-builder | ❌ 未验证 | |
| hoare-logic-verifier | ❌ 未验证 | |
| separation-logician | ❌ 未验证 | |
| coq-proof-assistant | ❌ 未验证 | |
| bisimulation-checker | ❌ 未验证 | |
| lambda-calculus-interpreter | ❌ 未验证 | |
| closure-converter | ❌ 未验证 | |
| lexer-generator | ❌ 未验证 | |
| parser-generator | ❌ 未验证 | |
| ssa-constructor | ❌ 未验证 | |
| jit-compiler-builder | ❌ 未验证 | |
| typed-assembly-language | ❌ 未验证 | |
| cps-transformer | ❌ 未验证 | |
| partial-evaluator | ❌ 未验证 | |
| defunctionalization | ❌ 未验证 | |
| multi-stage-programming | ❌ 未验证 | |
| dsl-embedding | ❌ 未验证 | |
| dataflow-analysis-framework | ❌ 未验证 | |
| abstract-interpretation-engine | ❌ 未验证 | |
| alias-and-points-to-analysis | ❌ 未验证 | |
| taint-analysis | ❌ 未验证 | |
| model-checker | ❌ 未验证 | |
| garbage-collector-implementer | ❌ 未验证 | |
| constant-propagation-pass | ❌ 未验证 | |
| common-subexpression-eliminator | ❌ 未验证 | |
| incremental-computation | ❌ 未验证 | |
| symbolic-execution-engine | ❌ 未验证 | |
| invariant-generator | ❌ 未验证 | |
| loop-termination-prover | ❌ 未验证 | |
| weak-memory-model-verifier | ❌ 未验证 | |
| actor-model-implementer | ❌ 未验证 | |
| software-transactional-memory | ❌ 未验证 | |
| race-detection-tool | ❌ 未验证 | |
| *(其他技能)* | ❌ 未验证 | |

**图例：** ✅ 已验证 | 🔶 部分验证 | ❌ 未验证

如需帮助验证技能，请参阅 [贡献指南](CONTRIBUTING.md)。

---

## 🌐 Skills Manager 网页界面

**[🚀 访问 Skills Manager](https://rainoftime.github.io/pl-skills/)**

通过交互式网页界面浏览、搜索和安装技能。

---

## 关于本仓库

本仓库包含 **99 个 PL 研究技能**，面向：

- **PL 研究者** — 类型系统、形式语义、证明助手
- **编译器实践者** — 编译器遍、程序分析、优化
- **系统工程师** — 运行时系统、验证、并发
- **研究生** — 通过可运行实现学习 PL 概念
- **工具开发者** — 构建编译器、分析器与验证器

每个技能都是**自包含实现**，可解决真实 PL 研究问题：
- 任务导向（解决具体 PL 问题）
- 可复用（输入/输出清晰约定）
- 工具感知（操作真实代码、规约与证明）

---

## 🎯 按主题分类的技能

### 🔬 类型系统与形式语义

| 技能 | 描述 |
|-------|-------------|
| [type-checker-generator](./type-checker-generator/) | 从语言规约生成类型检查器 |
| [type-inference-engine](./type-inference-engine/) | 实现 Hindley-Milner 类型推断 |
| [subtyping-verifier](./subtyping-verifier/) | 验证子类型关系 |
| [simply-typed-lambda-calculus](./simply-typed-lambda-calculus/) | 带积、和与布尔型的 STLC |
| [dependent-type-implementer](./dependent-type-implementer/) | 依赖类型（Pi、Sigma、相等） |
| [linear-type-implementer](./linear-type-implementer/) | 带资源的线性 λ 演算 |
| [session-type-checker](./session-type-checker/) | 通信协议的会话类型 |
| [ownership-type-system](./ownership-type-system/) | 所有权与借用（类 Rust） |
| [effect-type-system](./effect-type-system/) | 副作用的效果追踪 |
| [refinement-type-checker](./refinement-type-checker/) | 带谓词的 refinement 类型 |
| [relational-parametricity-prover](./relational-parametricity-prover/) | 证明参数化定理 |
| [bidirectional-type-checking](./bidirectional-type-checking/) | 双向类型推断/检查 |
| [row-polymorphism](./row-polymorphism/) | 带行类型的可扩展记录 |
| [polymorphic-effects](./polymorphic-effects/) | 效果多态与 handler |
| [higher-order-abstract-syntax](./higher-order-abstract-syntax/) | 用于 binder 表示的 HOAS |
| [type-directed-name-resolution](./type-directed-name-resolution/) | 类型引导的名称消歧 |

### 📐 形式语义

| 技能 | 描述 |
|-------|-------------|
| [operational-semantics-definer](./operational-semantics-definer/) | 为语言定义 SOS 语义 |
| [denotational-semantics-builder](./denotational-semantics-builder/) | 构建指称语义 |
| [hoare-logic-verifier](./hoare-logic-verifier/) | 用 Hoare 逻辑验证程序 |
| [separation-logician](./separation-logician/) | 堆验证的分离逻辑 |
| [coq-proof-assistant](./coq-proof-assistant/) | 在 Coq 中证明（归纳、策略） |
| [bisimulation-checker](./bisimulation-checker/) | 证明程序间双模拟 |

---

### ⚙️ 编译器与解释器

| 技能 | 描述 |
|-------|-------------|
| [lambda-calculus-interpreter](./lambda-calculus-interpreter/) | 无类型与简单类型 λ 演算 |
| [closure-converter](./closure-converter/) | 将闭包变换为环境传递 |
| [lexer-generator](./lexer-generator/) | 生成词法分析器 |
| [parser-generator](./parser-generator/) | 生成 LALR/递归下降解析器 |
| [ssa-constructor](./ssa-constructor/) | 构建 SSA 形式 |
| [jit-compiler-builder](./jit-compiler-builder/) | JIT 编译基础设施 |
| [typed-assembly-language](./typed-assembly-language/) | 类型化汇编语言验证器 |
| [cps-transformer](./cps-transformer/) |  continuation 传递风格变换 |
| [partial-evaluator](./partial-evaluator/) | 通过部分求值做程序特化 |
| [defunctionalization](./defunctionalization/) | 闭包消除为数据类型 |
| [multi-stage-programming](./multi-stage-programming/) | 分阶段编译与代码生成 |
| [dsl-embedding](./dsl-embedding/) | 在宿主语言中嵌入 DSL |

### 📊 程序分析

| 技能 | 描述 |
|-------|-------------|
| [dataflow-analysis-framework](./dataflow-analysis-framework/) | 通用数据流分析框架 |
| [abstract-interpretation-engine](./abstract-interpretation-engine/) | 抽象解释引擎 |
| [alias-and-points-to-analysis](./alias-and-points-to-analysis/) | 指向与别名分析 |
| [taint-analysis](./taint-analysis/) | 安全相关的污点追踪 |
| [model-checker](./model-checker/) | 有限状态模型检测 |

---

### ⚡ 运行时与优化

| 技能 | 描述 |
|-------|-------------|
| [garbage-collector-implementer](./garbage-collector-implementer/) | GC（标记-压缩、分代） |
| [constant-propagation-pass](./constant-propagation-pass/) | 数据流常量传播 |
| [common-subexpression-eliminator](./common-subexpression-eliminator/) | CSE 优化遍 |
| [incremental-computation](./incremental-computation/) | 变更传播与自适应计算 |

### 🔒 验证

| 技能 | 描述 |
|-------|-------------|
| [symbolic-execution-engine](./symbolic-execution-engine/) | 符号执行引擎 |
| [invariant-generator](./invariant-generator/) | 推断循环不变量 |
| [loop-termination-prover](./loop-termination-prover/) | 证明循环终止性 |
| [weak-memory-model-verifier](./weak-memory-model-verifier/) | 验证弱内存行为 |

### 🔀 并发

| 技能 | 描述 |
|-------|-------------|
| [actor-model-implementer](./actor-model-implementer/) | Actor 并发模型 |
| [software-transactional-memory](./software-transactional-memory/) | STM 实现 |
| [race-detection-tool](./race-detection-tool/) | 动态竞态检测 |

---

## 📖 使用方法

每个技能以包含 `SKILL.md` 的文件夹形式提供。

### 安装技能

```bash
# 将技能文件夹复制到技能目录
cp -r skill-folder ~/.claude/skills
```

### 使用技能

技能会根据与描述匹配的用户请求自动触发，也可显式调用：

> 使用 "type-checker-generator" 为我的语言生成类型检查器

---

## 🤝 贡献

我们欢迎来自以下方面的贡献：
- **PL 研究者**（类型系统、语义、验证相关新技能）
- **编译器开发者**（优化遍、分析框架）
- **形式化方法实践者**（证明助手、模型检测器）

提交前请阅读 [贡献指南](CONTRIBUTING.md)。

---

## 📚 参考

技能灵感来源：
- [awesome-claude-skills](https://github.com/ComposioHQ/awesome-claude-skills/)
- [anthropics-skills](https://github.com/anthropics/skills/)

---

## 🔄 流水线

由多个技能组成的端到端工作流：

| 流水线 | 描述 |
|----------|-------------|
| [compiler-pipeline](./pipelines/compiler-pipeline.md) | 从源码到本地代码构建编译器 |
| [verification-pipeline](./pipelines/verification-pipeline.md) | 验证程序正确性 |
| [type-system-pipeline](./pipelines/type-system-pipeline.md) | 实现完整类型系统 |

详见 [pipelines/](./pipelines/)。
