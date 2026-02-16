#!/usr/bin/env python3
"""
Add standardized metadata to all SKILL.md files.
"""

import os
import yaml
from pathlib import Path
from typing import Dict, List, Optional

REPO_ROOT = Path(__file__).parent.parent

SKILL_METADATA = {
    'lambda-calculus-interpreter': {
        'tags': ['interpreter', 'lambda-calculus', 'functional-programming', 'foundations'],
        'difficulty': 'beginner',
        'languages': ['python'],
        'dependencies': []
    },
    'type-checker-generator': {
        'tags': ['type-systems', 'type-checking', 'compiler', 'static-analysis'],
        'difficulty': 'intermediate',
        'languages': ['python', 'ocaml'],
        'dependencies': ['lambda-calculus-interpreter']
    },
    'type-inference-engine': {
        'tags': ['type-systems', 'type-inference', 'hindley-milner', 'unification'],
        'difficulty': 'intermediate',
        'languages': ['python', 'ocaml'],
        'dependencies': ['type-checker-generator']
    },
    'subtyping-verifier': {
        'tags': ['type-systems', 'subtyping', 'inheritance', 'polymorphism'],
        'difficulty': 'intermediate',
        'languages': ['python', 'ocaml'],
        'dependencies': ['type-checker-generator']
    },
    'simply-typed-lambda-calculus': {
        'tags': ['type-systems', 'lambda-calculus', 'stlc', 'foundations'],
        'difficulty': 'beginner',
        'languages': ['python', 'ocaml', 'haskell'],
        'dependencies': ['lambda-calculus-interpreter']
    },
    'dependent-type-implementer': {
        'tags': ['type-systems', 'dependent-types', 'type-theory', 'proofs'],
        'difficulty': 'advanced',
        'languages': ['python', 'agda', 'idris'],
        'dependencies': ['simply-typed-lambda-calculus']
    },
    'linear-type-implementer': {
        'tags': ['type-systems', 'linear-types', 'resource-management', 'rust'],
        'difficulty': 'advanced',
        'languages': ['python', 'rust', 'haskell'],
        'dependencies': ['simply-typed-lambda-calculus']
    },
    'session-type-checker': {
        'tags': ['type-systems', 'concurrency', 'session-types', 'communication'],
        'difficulty': 'advanced',
        'languages': ['python', 'haskell'],
        'dependencies': ['linear-type-implementer']
    },
    'ownership-type-system': {
        'tags': ['type-systems', 'ownership', 'borrowing', 'rust'],
        'difficulty': 'advanced',
        'languages': ['python', 'rust'],
        'dependencies': ['linear-type-implementer']
    },
    'effect-type-system': {
        'tags': ['type-systems', 'effects', 'side-effects', 'monads'],
        'difficulty': 'intermediate',
        'languages': ['python', 'haskell'],
        'dependencies': ['type-checker-generator']
    },
    'refinement-type-checker': {
        'tags': ['type-systems', 'refinement-types', 'verification', 'smt'],
        'difficulty': 'advanced',
        'languages': ['python', 'z3'],
        'dependencies': ['type-checker-generator']
    },
    'relational-parametricity-prover': {
        'tags': ['type-theory', 'parametricity', 'proofs', 'polymorphism'],
        'difficulty': 'advanced',
        'languages': ['coq', 'agda'],
        'dependencies': ['coq-proof-assistant']
    },
    'bidirectional-type-checking': {
        'tags': ['type-systems', 'type-inference', 'bidirectional', 'type-checking'],
        'difficulty': 'intermediate',
        'languages': ['python', 'ocaml', 'haskell'],
        'dependencies': ['type-checker-generator']
    },
    'row-polymorphism': {
        'tags': ['type-systems', 'row-polymorphism', 'records', 'extensibility'],
        'difficulty': 'intermediate',
        'languages': ['python', 'ocaml'],
        'dependencies': ['type-inference-engine']
    },
    'polymorphic-effects': {
        'tags': ['type-systems', 'effects', 'polymorphism', 'handlers'],
        'difficulty': 'advanced',
        'languages': ['python', 'haskell'],
        'dependencies': ['effect-type-system']
    },
    'higher-order-abstract-syntax': {
        'tags': ['metaprogramming', 'hoas', 'binders', 'syntax'],
        'difficulty': 'intermediate',
        'languages': ['haskell', 'ocaml', 'scheme'],
        'dependencies': ['lambda-calculus-interpreter']
    },
    'type-directed-name-resolution': {
        'tags': ['type-systems', 'name-resolution', 'overloading', 'disambiguation'],
        'difficulty': 'intermediate',
        'languages': ['python', 'ocaml'],
        'dependencies': ['type-checker-generator']
    },
    'operational-semantics-definer': {
        'tags': ['semantics', 'operational-semantics', 'pl-foundations', 'language-design'],
        'difficulty': 'intermediate',
        'languages': ['ocaml', 'coq', 'python'],
        'dependencies': []
    },
    'denotational-semantics-builder': {
        'tags': ['semantics', 'denotational-semantics', 'domain-theory', 'pl-foundations'],
        'difficulty': 'advanced',
        'languages': ['haskell', 'coq'],
        'dependencies': ['operational-semantics-definer']
    },
    'hoare-logic-verifier': {
        'tags': ['verification', 'hoare-logic', 'program-proving', 'correctness'],
        'difficulty': 'intermediate',
        'languages': ['python', 'coq', 'why3'],
        'dependencies': ['operational-semantics-definer']
    },
    'separation-logician': {
        'tags': ['verification', 'separation-logic', 'heap-reasoning', 'memory-safety'],
        'difficulty': 'advanced',
        'languages': ['python', 'coq', 'verifast'],
        'dependencies': ['hoare-logic-verifier']
    },
    'coq-proof-assistant': {
        'tags': ['proof-assistant', 'coq', 'formal-verification', 'dependent-types'],
        'difficulty': 'intermediate',
        'languages': ['coq'],
        'dependencies': []
    },
    'lean-prover': {
        'tags': ['proof-assistant', 'lean', 'formal-verification', 'dependent-types'],
        'difficulty': 'intermediate',
        'languages': ['lean'],
        'dependencies': []
    },
    'bisimulation-checker': {
        'tags': ['semantics', 'bisimulation', 'equivalence', 'process-calculus'],
        'difficulty': 'intermediate',
        'languages': ['python', 'ocaml', 'coq'],
        'dependencies': ['operational-semantics-definer']
    },
    'closure-converter': {
        'tags': ['compiler', 'closures', 'code-generation', 'functional'],
        'difficulty': 'intermediate',
        'languages': ['python', 'ocaml', 'rust'],
        'dependencies': ['lambda-calculus-interpreter']
    },
    'lexer-generator': {
        'tags': ['compiler', 'lexing', 'parsing', 'frontend'],
        'difficulty': 'beginner',
        'languages': ['python', 'ocaml', 'rust'],
        'dependencies': []
    },
    'parser-generator': {
        'tags': ['compiler', 'parsing', 'grammars', 'frontend'],
        'difficulty': 'intermediate',
        'languages': ['python', 'ocaml', 'rust'],
        'dependencies': ['lexer-generator']
    },
    'ssa-constructor': {
        'tags': ['compiler', 'ssa', 'optimization', 'intermediate-representation'],
        'difficulty': 'intermediate',
        'languages': ['python', 'rust', 'c++'],
        'dependencies': []
    },
    'jit-compiler-builder': {
        'tags': ['compiler', 'jit', 'runtime', 'optimization'],
        'difficulty': 'advanced',
        'languages': ['rust', 'c++', 'llvm'],
        'dependencies': ['llvm-backend-generator', 'ssa-constructor']
    },
    'typed-assembly-language': {
        'tags': ['compiler', 'typed-assembly', 'low-level', 'verification'],
        'difficulty': 'advanced',
        'languages': ['assembly', 'coq'],
        'dependencies': ['type-checker-generator']
    },
    'cps-transformer': {
        'tags': ['compiler', 'cps', 'continuations', 'transformation'],
        'difficulty': 'intermediate',
        'languages': ['python', 'scheme', 'ocaml'],
        'dependencies': ['lambda-calculus-interpreter']
    },
    'partial-evaluator': {
        'tags': ['compiler', 'partial-evaluation', 'optimization', 'specialization'],
        'difficulty': 'intermediate',
        'languages': ['python', 'scheme'],
        'dependencies': []
    },
    'defunctionalization': {
        'tags': ['compiler', 'defunctionalization', 'first-order', 'transformation'],
        'difficulty': 'intermediate',
        'languages': ['python', 'ocaml'],
        'dependencies': ['closure-converter']
    },
    'multi-stage-programming': {
        'tags': ['metaprogramming', 'staging', 'code-generation', 'templates'],
        'difficulty': 'advanced',
        'languages': ['ocaml', 'rust', 'metaocaml'],
        'dependencies': ['partial-evaluator']
    },
    'dsl-embedding': {
        'tags': ['dsl', 'embedding', 'metaprogramming', 'domain-specific'],
        'difficulty': 'intermediate',
        'languages': ['haskell', 'scala', 'rust'],
        'dependencies': []
    },
    'llvm-backend-generator': {
        'tags': ['compiler', 'llvm', 'code-generation', 'backend'],
        'difficulty': 'intermediate',
        'languages': ['python', 'llvm', 'c++'],
        'dependencies': ['ssa-constructor']
    },
    'dataflow-analysis-framework': {
        'tags': ['static-analysis', 'dataflow', 'lattice', 'analysis'],
        'difficulty': 'intermediate',
        'languages': ['python', 'ocaml'],
        'dependencies': []
    },
    'abstract-interpretation-engine': {
        'tags': ['static-analysis', 'abstract-interpretation', 'fixpoint', 'verification'],
        'difficulty': 'advanced',
        'languages': ['python', 'ocaml'],
        'dependencies': ['dataflow-analysis-framework']
    },
    'alias-and-points-to-analysis': {
        'tags': ['static-analysis', 'alias-analysis', 'points-to-analysis', 'pointers', 'optimization'],
        'difficulty': 'intermediate',
        'languages': ['python', 'c++', 'rust'],
        'dependencies': ['dataflow-analysis-framework']
    },
    'taint-analysis': {
        'tags': ['static-analysis', 'taint-analysis', 'security', 'information-flow'],
        'difficulty': 'intermediate',
        'languages': ['python'],
        'dependencies': ['dataflow-analysis-framework']
    },
    'model-checker': {
        'tags': ['verification', 'model-checking', 'temporal-logic', 'state-space'],
        'difficulty': 'advanced',
        'languages': ['python', 'ocaml'],
        'dependencies': []
    },
    'garbage-collector-implementer': {
        'tags': ['runtime', 'garbage-collection', 'memory-management', 'systems'],
        'difficulty': 'intermediate',
        'languages': ['c', 'rust', 'c++'],
        'dependencies': []
    },
    'constant-propagation-pass': {
        'tags': ['optimization', 'compiler-pass', 'dataflow', 'constant-folding'],
        'difficulty': 'beginner',
        'languages': ['python', 'rust'],
        'dependencies': ['dataflow-analysis-framework']
    },
    'common-subexpression-eliminator': {
        'tags': ['optimization', 'compiler-pass', 'cse', 'code-motion'],
        'difficulty': 'intermediate',
        'languages': ['python', 'rust'],
        'dependencies': ['ssa-constructor']
    },
    'incremental-computation': {
        'tags': ['optimization', 'incremental', 'change-propagation', 'self-adjusting'],
        'difficulty': 'advanced',
        'languages': ['python', 'ocaml'],
        'dependencies': []
    },
    'symbolic-execution-engine': {
        'tags': ['verification', 'symbolic-execution', 'smt', 'testing'],
        'difficulty': 'advanced',
        'languages': ['python', 'z3'],
        'dependencies': []
    },
    'invariant-generator': {
        'tags': ['verification', 'invariants', 'induction', 'program-analysis'],
        'difficulty': 'advanced',
        'languages': ['python', 'z3'],
        'dependencies': ['abstract-interpretation-engine']
    },
    'loop-termination-prover': {
        'tags': ['verification', 'termination', 'ranking-functions', 'loops'],
        'difficulty': 'advanced',
        'languages': ['python', 'z3', 'coq'],
        'dependencies': ['invariant-generator']
    },
    'weak-memory-model-verifier': {
        'tags': ['verification', 'memory-models', 'concurrency', 'relaxed'],
        'difficulty': 'advanced',
        'languages': ['python', 'coq'],
        'dependencies': ['model-checker']
    },
    'actor-model-implementer': {
        'tags': ['concurrency', 'actor-model', 'distributed', 'message-passing'],
        'difficulty': 'intermediate',
        'languages': ['python', 'rust', 'erlang'],
        'dependencies': []
    },
    'software-transactional-memory': {
        'tags': ['concurrency', 'stm', 'transactions', 'synchronization'],
        'difficulty': 'intermediate',
        'languages': ['haskell', 'rust'],
        'dependencies': []
    },
    'race-detection-tool': {
        'tags': ['concurrency', 'race-detection', 'static-analysis', 'threading'],
        'difficulty': 'intermediate',
        'languages': ['python', 'rust'],
        'dependencies': ['alias-and-points-to-analysis']
    },
    'effect-handlers-implementer': {
        'tags': ['effects', 'handlers', 'control-flow', 'algebraic-effects'],
        'difficulty': 'advanced',
        'languages': ['python', 'haskell', 'ocaml'],
        'dependencies': ['effect-type-system']
    },
    'gradual-typing-implementer': {
        'tags': ['type-systems', 'gradual-typing', 'dynamic-typing', 'hybrid'],
        'difficulty': 'advanced',
        'languages': ['python', 'racket', 'typescript'],
        'dependencies': ['type-checker-generator']
    },
    'webassembly-verifier': {
        'tags': ['verification', 'webassembly', 'bytecode', 'sandboxing'],
        'difficulty': 'intermediate',
        'languages': ['python', 'rust'],
        'dependencies': []
    },
    'graalvm-truffle-implementer': {
        'tags': ['runtime', 'graalvm', 'truffle', 'polyglot'],
        'difficulty': 'advanced',
        'languages': ['java', 'truffle'],
        'dependencies': []
    },
    'mlir-dialect-designer': {
        'tags': ['compiler', 'mlir', 'dialects', 'llvm'],
        'difficulty': 'advanced',
        'languages': ['c++', 'mlir'],
        'dependencies': ['llvm-backend-generator']
    },
    'rust-borrow-checker': {
        'tags': ['type-systems', 'borrow-checker', 'ownership', 'rust'],
        'difficulty': 'advanced',
        'languages': ['rust'],
        'dependencies': ['ownership-type-system']
    },
    'webassembly-runtime': {
        'tags': ['runtime', 'webassembly', 'wasm', 'execution'],
        'difficulty': 'intermediate',
        'languages': ['rust', 'c++'],
        'dependencies': ['webassembly-verifier']
    },
    'value-analysis': {
        'tags': ['static-analysis', 'value-analysis', 'numerical', 'abstract-domains'],
        'difficulty': 'intermediate',
        'languages': ['python'],
        'dependencies': ['abstract-interpretation-engine']
    },
    'program-transformer': {
        'tags': ['transformation', 'refactoring', 'metaprogramming', 'rewriting'],
        'difficulty': 'intermediate',
        'languages': ['python', 'ocaml'],
        'dependencies': []
    },
    'interprocedural-analysis': {
        'tags': ['static-analysis', 'interprocedural', 'call-graph', 'context'],
        'difficulty': 'advanced',
        'languages': ['python', 'ocaml'],
        'dependencies': ['dataflow-analysis-framework']
    },
    'control-flow-analysis': {
        'tags': ['static-analysis', 'control-flow', 'cfg', 'higher-order'],
        'difficulty': 'intermediate',
        'languages': ['python', 'ocaml'],
        'dependencies': ['dataflow-analysis-framework']
    },
    'contextual-equivalence': {
        'tags': ['semantics', 'equivalence', 'context', 'program-equivalence'],
        'difficulty': 'advanced',
        'languages': ['coq', 'ocaml'],
        'dependencies': ['operational-semantics-definer']
    },
    'acsl-annotation-assistant': {
        'tags': ['verification', 'frama-c', 'acsl', 'c-verification'],
        'difficulty': 'intermediate',
        'languages': ['c', 'acsl'],
        'dependencies': ['hoare-logic-verifier']
    }
}


def add_metadata_to_skill(skill_dir: Path) -> bool:
    """Add standardized metadata to a skill's SKILL.md file."""
    skill_name = skill_dir.name
    skill_md = skill_dir / 'SKILL.md'
    
    if not skill_md.exists():
        print(f"Skipping {skill_name}: no SKILL.md")
        return False
    
    with open(skill_md, 'r', encoding='utf-8') as f:
        content = f.read()
    
    if not content.startswith('---'):
        print(f"Skipping {skill_name}: no frontmatter")
        return False
    
    parts = content.split('---', 2)
    if len(parts) < 3:
        print(f"Skipping {skill_name}: invalid frontmatter")
        return False
    
    try:
        frontmatter = yaml.safe_load(parts[1])
        if frontmatter is None:
            frontmatter = {}
    except yaml.YAMLError as e:
        print(f"Skipping {skill_name}: YAML error: {e}")
        return False
    
    metadata = SKILL_METADATA.get(skill_name, {})
    if not metadata:
        print(f"No metadata defined for {skill_name}")
        return False
    
    updated = False
    
    if 'version' not in frontmatter:
        frontmatter['version'] = '1.0.0'
        updated = True
    
    if 'tags' not in frontmatter and 'tags' in metadata:
        frontmatter['tags'] = metadata['tags']
        updated = True
    
    if 'difficulty' not in frontmatter and 'difficulty' in metadata:
        frontmatter['difficulty'] = metadata['difficulty']
        updated = True
    
    if 'languages' not in frontmatter and 'languages' in metadata:
        frontmatter['languages'] = metadata['languages']
        updated = True
    
    if 'dependencies' not in frontmatter and 'dependencies' in metadata:
        frontmatter['dependencies'] = metadata['dependencies']
        updated = True
    
    if not updated:
        print(f"No updates needed for {skill_name}")
        return False
    
    new_content = '---\n' + yaml.dump(frontmatter, sort_keys=False, allow_unicode=True) + '---' + parts[2]
    
    with open(skill_md, 'w', encoding='utf-8') as f:
        f.write(new_content)
    
    print(f"Updated {skill_name}")
    return True


def main():
    """Update all skills with metadata."""
    print("=" * 60)
    print("Adding metadata to skills")
    print("=" * 60 + "\n")
    
    updated_count = 0
    
    for item in sorted(REPO_ROOT.iterdir()):
        if item.is_dir() and not item.name.startswith('.') and item.name != 'template' and item.name != 'scripts':
            if (item / 'SKILL.md').exists():
                if add_metadata_to_skill(item):
                    updated_count += 1
    
    print(f"\n{'=' * 60}")
    print(f"Updated {updated_count} skills")
    print("=" * 60)


if __name__ == '__main__':
    main()
