#!/usr/bin/env python3
"""
Fix broken cross-references in SKILL.md files.
"""

import re
from pathlib import Path

REPO_ROOT = Path(__file__).parent.parent

# Mapping of broken references to replacements
REPLACEMENTS = {
    'type-soundness-prover': 'hoare-logic-verifier',
    'verified-compiler-builder': 'llvm-backend-generator',
    'virtual-machine-designer': 'jit-compiler-builder',
    'stack-machine-interpreter': 'lambda-calculus-interpreter',
    'continuation-implementer': 'cps-transformer',
    'dead-code-eliminator-pass': 'common-subexpression-eliminator',
    'pointer-analysis-engine': 'alias-and-points-to-analysis',
    'register-allocator': 'ssa-constructor',
    'dataflow-analyzer': 'dataflow-analysis-framework',
    'bounded-model-checker': 'model-checker',
    'concurrent-program-verifier': 'weak-memory-model-verifier',
    'memory-safety-verifier': 'separation-logician',
    'system-f-implementer': 'dependent-type-implementer',
    'calculus-of-constructions-builder': 'dependent-type-implementer',
    'happen-before-analyzer': 'race-detection-tool',
    'heap-layout-calculator': 'garbage-collector-implementer',
    'interpreter-builder': 'lambda-calculus-interpreter',
    'security-type-checker': 'taint-analysis',
    'sandbox-executor': 'webassembly-runtime',
    'static-analysis-tool': 'dataflow-analysis-framework',
    'ast-transformer': 'program-transformer',
    'compiler-pipeline-designer': 'llvm-backend-generator',
    'gradual-typing-advisor': 'gradual-typing-implementer',
    'related-skill-1': None,  # Remove placeholder
    'related-skill-2': None,  # Remove placeholder
}

def fix_file(skill_md: Path) -> bool:
    """Fix broken references in a file."""
    with open(skill_md, 'r', encoding='utf-8') as f:
        content = f.read()
    
    original = content
    
    for broken, replacement in REPLACEMENTS.items():
        pattern = f'`{broken}`'
        if pattern in content:
            if replacement:
                content = content.replace(pattern, f'`{replacement}`')
                print(f"  Replaced `{broken}` -> `{replacement}`")
            else:
                # Remove the line containing the broken reference
                lines = content.split('\n')
                new_lines = []
                for line in lines:
                    if pattern in line:
                        print(f"  Removed line with `{broken}`")
                        continue
                    new_lines.append(line)
                content = '\n'.join(new_lines)
    
    if content != original:
        with open(skill_md, 'w', encoding='utf-8') as f:
            f.write(content)
        return True
    return False


def main():
    print("Fixing broken cross-references...")
    print("=" * 60)
    
    fixed_count = 0
    
    for item in sorted(REPO_ROOT.iterdir()):
        if item.is_dir() and not item.name.startswith('.') and item.name not in ['template', 'scripts', 'skill-manager']:
            skill_md = item / 'SKILL.md'
            if skill_md.exists():
                print(f"\nChecking {item.name}...")
                if fix_file(skill_md):
                    fixed_count += 1
    
    print(f"\n{'=' * 60}")
    print(f"Fixed {fixed_count} files")


if __name__ == '__main__':
    main()
