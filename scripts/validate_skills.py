#!/usr/bin/env python3
"""
Validate SKILL.md files in the repository.
Checks:
1. YAML frontmatter exists and is valid
2. Required fields are present (name, description)
3. Optional fields are valid (tags, difficulty, languages, dependencies)
4. Sections are present
5. Cross-references exist
"""

import os
import sys
import yaml
import re
from pathlib import Path
from typing import Dict, List, Tuple, Optional

REPO_ROOT = Path(__file__).parent.parent

REQUIRED_FRONTMATTER = ['name', 'description']
OPTIONAL_FRONTMATTER = ['version', 'tags', 'difficulty', 'languages', 'dependencies']
VALID_DIFFICULTIES = ['beginner', 'intermediate', 'advanced']
REQUIRED_SECTIONS = [
    '## When to Use',
    '## What This Skill Does',
    '## How to Use',
]

RECOMMENDED_SECTIONS = [
    '## Tips',
    '## Related Skills',
    '## Tradeoffs and Limitations',
    '## Assessment Criteria',
]


def find_all_skills() -> List[Path]:
    """Find all skill directories with SKILL.md files."""
    skills = []
    for item in REPO_ROOT.iterdir():
        if item.is_dir() and not item.name.startswith('.'):
            skill_md = item / 'SKILL.md'
            if skill_md.exists():
                skills.append(item)
    return sorted(skills)


def parse_frontmatter(content: str) -> Tuple[Optional[Dict], str, List[str]]:
    """Parse YAML frontmatter from SKILL.md content."""
    errors = []
    
    if not content.startswith('---'):
        return None, content, ['Missing YAML frontmatter (should start with ---)']
    
    parts = content.split('---', 2)
    if len(parts) < 3:
        return None, content, ['Invalid frontmatter format (missing closing ---)']
    
    try:
        frontmatter = yaml.safe_load(parts[1])
        if frontmatter is None:
            frontmatter = {}
    except yaml.YAMLError as e:
        return None, content, [f'YAML parsing error: {e}']
    
    return frontmatter, parts[2], errors


def validate_frontmatter(frontmatter: Dict, skill_name: str) -> List[str]:
    """Validate frontmatter fields."""
    errors = []
    warnings = []
    
    for field in REQUIRED_FRONTMATTER:
        if field not in frontmatter:
            errors.append(f'Missing required field: {field}')
    
    if 'difficulty' in frontmatter:
        if frontmatter['difficulty'] not in VALID_DIFFICULTIES:
            errors.append(f"Invalid difficulty '{frontmatter['difficulty']}', must be one of: {VALID_DIFFICULTIES}")
    
    if 'tags' in frontmatter:
        if not isinstance(frontmatter['tags'], list):
            errors.append('tags must be a list')
    
    if 'languages' in frontmatter:
        if not isinstance(frontmatter['languages'], list):
            errors.append('languages must be a list')
    
    if 'dependencies' in frontmatter:
        if not isinstance(frontmatter['dependencies'], list):
            errors.append('dependencies must be a list')
    
    for field in OPTIONAL_FRONTMATTER:
        if field not in frontmatter:
            warnings.append(f'Missing optional field: {field}')
    
    return errors + [f'Warning: {w}' for w in warnings]


def validate_sections(content: str) -> List[str]:
    """Validate that required sections exist."""
    errors = []
    warnings = []
    
    for section in REQUIRED_SECTIONS:
        if section not in content:
            errors.append(f'Missing required section: {section}')
    
    for section in RECOMMENDED_SECTIONS:
        if section not in content:
            warnings.append(f'Missing recommended section: {section}')
    
    return errors + [f'Warning: {w}' for w in warnings]


def extract_cross_references(content: str) -> List[str]:
    """Extract skill names from Related Skills section."""
    refs = []
    pattern = r'`([a-z0-9-]+)`'
    
    lines = content.split('\n')
    in_related = False
    
    for line in lines:
        if '## Related Skills' in line:
            in_related = True
            continue
        if in_related and line.startswith('## '):
            in_related = False
        if in_related:
            matches = re.findall(pattern, line)
            refs.extend(matches)
    
    return refs


def validate_cross_references(skill_dir: Path, all_skills: List[str], content: str) -> List[str]:
    """Validate that cross-references point to existing skills."""
    errors = []
    refs = extract_cross_references(content)
    
    for ref in refs:
        if ref not in all_skills:
            errors.append(f'Broken cross-reference: `{ref}` does not exist')
    
    return errors


def validate_skill(skill_dir: Path, all_skills: List[str]) -> Tuple[bool, List[str]]:
    """Validate a single skill directory."""
    skill_name = skill_dir.name
    skill_md = skill_dir / 'SKILL.md'
    
    errors = []
    
    with open(skill_md, 'r', encoding='utf-8') as f:
        content = f.read()
    
    frontmatter, body, fm_errors = parse_frontmatter(content)
    errors.extend(fm_errors)
    
    if frontmatter:
        errors.extend(validate_frontmatter(frontmatter, skill_name))
    
    errors.extend(validate_sections(body))
    errors.extend(validate_cross_references(skill_dir, all_skills, body))
    
    return len([e for e in errors if not e.startswith('Warning')]) == 0, errors


def main():
    """Main validation function."""
    print("=" * 60)
    print("SKILL.md Validation")
    print("=" * 60)
    
    skills = find_all_skills()
    all_skill_names = [s.name for s in skills]
    
    print(f"\nFound {len(skills)} skills to validate.\n")
    
    all_passed = True
    error_count = 0
    warning_count = 0
    
    for skill_dir in skills:
        passed, messages = validate_skill(skill_dir, all_skill_names)
        
        if not passed:
            all_passed = False
            print(f"\n❌ {skill_dir.name}")
            for msg in messages:
                if msg.startswith('Warning'):
                    warning_count += 1
                    print(f"   ⚠️  {msg}")
                else:
                    error_count += 1
                    print(f"   ❌ {msg}")
        elif any(m.startswith('Warning') for m in messages):
            print(f"\n✅ {skill_dir.name} (with warnings)")
            for msg in messages:
                if msg.startswith('Warning'):
                    warning_count += 1
                    print(f"   ⚠️  {msg}")
        else:
            print(f"✅ {skill_dir.name}")
    
    print("\n" + "=" * 60)
    print(f"Summary: {len(skills)} skills validated")
    print(f"Errors: {error_count}")
    print(f"Warnings: {warning_count}")
    print("=" * 60)
    
    if not all_passed:
        sys.exit(1)
    
    print("\n✅ All validations passed!")


if __name__ == '__main__':
    main()
