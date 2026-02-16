from flask import Flask, jsonify, request
from flask_cors import CORS
import os
import shutil
import yaml
from pathlib import Path
from typing import Dict, List, Optional, Set
from collections import defaultdict

app = Flask(__name__)
CORS(app)

REPO_ROOT = Path(__file__).parent.parent.parent
SKILLS_DIR = REPO_ROOT
CLAUDE_SKILLS_DIR = Path.home() / '.claude' / 'skills'


def get_skill_metadata(skill_path: Path) -> Optional[Dict]:
    """Extract metadata from SKILL.md file."""
    skill_md = skill_path / 'SKILL.md'
    if not skill_md.exists():
        return None

    try:
        with open(skill_md, 'r', encoding='utf-8') as f:
            content = f.read()

        if content.startswith('---'):
            parts = content.split('---', 2)
            if len(parts) >= 3:
                frontmatter = yaml.safe_load(parts[1]) or {}
                
                description = frontmatter.get('description', '')
                if len(description) > 200:
                    description = description[:200] + '...'
                
                return {
                    'name': frontmatter.get('name', skill_path.name),
                    'description': description,
                    'version': frontmatter.get('version', '1.0.0'),
                    'tags': frontmatter.get('tags', []),
                    'difficulty': frontmatter.get('difficulty', 'intermediate'),
                    'languages': frontmatter.get('languages', []),
                    'dependencies': frontmatter.get('dependencies', []),
                }
    except Exception as e:
        print(f"Error reading {skill_path.name}: {e}")

    return None


def is_skill_installed(skill_name: str) -> bool:
    """Check if skill is already installed."""
    return (CLAUDE_SKILLS_DIR / skill_name).exists()


def get_all_tags(skills: List[Dict]) -> List[str]:
    """Get all unique tags from skills."""
    tags = set()
    for skill in skills:
        tags.update(skill.get('tags', []))
    return sorted(tags)


def get_all_languages(skills: List[Dict]) -> List[str]:
    """Get all unique languages from skills."""
    languages = set()
    for skill in skills:
        languages.update(skill.get('languages', []))
    return sorted(languages)


def get_skill_category(skill: Dict) -> str:
    """Determine skill category based on tags."""
    tags = set(skill.get('tags', []))
    
    if 'type-systems' in tags or 'type-theory' in tags:
        return 'type-systems'
    if 'semantics' in tags:
        return 'semantics'
    if 'compiler' in tags:
        return 'compiler'
    if 'static-analysis' in tags:
        return 'static-analysis'
    if 'verification' in tags:
        return 'verification'
    if 'concurrency' in tags:
        return 'concurrency'
    if 'proof-assistant' in tags:
        return 'proof-assistant'
    if 'runtime' in tags:
        return 'runtime'
    if 'optimization' in tags:
        return 'optimization'
    if 'metaprogramming' in tags or 'dsl' in tags:
        return 'metaprogramming'
    if 'interpreter' in tags:
        return 'interpreter'
    if 'transformation' in tags:
        return 'transformation'
    
    return 'other'


def get_dependency_order(skills: List[str], all_skills: Dict[str, Dict]) -> List[str]:
    """Get skills in dependency order (topological sort)."""
    visited = set()
    result = []
    
    def visit(skill_name: str):
        if skill_name in visited:
            return
        if skill_name not in all_skills:
            return
        
        visited.add(skill_name)
        
        for dep in all_skills[skill_name].get('dependencies', []):
            if dep in skills:
                visit(dep)
        
        result.append(skill_name)
    
    for skill in skills:
        visit(skill)
    
    return result


@app.route('/api/skills', methods=['GET'])
def get_skills():
    """Get list of all available skills."""
    skills = []
    excluded_dirs = {'skill-manager', 'node_modules', 'skill-creator', 'scripts', 'template', 'pipelines', '.venv'}

    for item in SKILLS_DIR.iterdir():
        if item.is_dir() and not item.name.startswith('.') and item.name not in excluded_dirs:
            if (item / 'SKILL.md').exists():
                metadata = get_skill_metadata(item)
                if metadata:
                    skill_data = {
                        'name': item.name,
                        'description': metadata['description'],
                        'version': metadata['version'],
                        'tags': metadata['tags'],
                        'difficulty': metadata['difficulty'],
                        'languages': metadata['languages'],
                        'dependencies': metadata['dependencies'],
                        'installed': is_skill_installed(item.name),
                        'path': str(item),
                        'category': None  # Will be computed
                    }
                    skill_data['category'] = get_skill_category(skill_data)
                    skills.append(skill_data)

    all_tags = get_all_tags(skills)
    all_languages = get_all_languages(skills)
    
    return jsonify({
        'skills': sorted(skills, key=lambda x: x['name']),
        'total': len(skills),
        'tags': all_tags,
        'languages': all_languages,
        'categories': ['type-systems', 'semantics', 'compiler', 'static-analysis', 
                       'verification', 'concurrency', 'proof-assistant', 'runtime',
                       'optimization', 'metaprogramming', 'interpreter', 'transformation', 'other']
    })


@app.route('/api/skills/<skill_name>', methods=['GET'])
def get_skill_detail(skill_name: str):
    """Get detailed information about a specific skill."""
    skill_path = SKILLS_DIR / skill_name
    
    if not skill_path.exists():
        return jsonify({'error': 'Skill not found'}), 404
    
    metadata = get_skill_metadata(skill_path)
    if not metadata:
        return jsonify({'error': 'Invalid skill'}), 400
    
    skill_md = skill_path / 'SKILL.md'
    with open(skill_md, 'r', encoding='utf-8') as f:
        content = f.read()
    
    return jsonify({
        'name': skill_name,
        'metadata': metadata,
        'installed': is_skill_installed(skill_name),
        'path': str(skill_path),
        'content': content
    })


@app.route('/api/install', methods=['POST'])
def install_skills():
    """Install selected skills to Claude skills directory with dependency resolution."""
    data = request.json
    skill_names = data.get('skills', [])
    resolve_deps = data.get('resolveDependencies', True)

    if not skill_names:
        return jsonify({'error': 'No skills specified'}), 400

    # Build skill metadata map
    all_skills = {}
    for item in SKILLS_DIR.iterdir():
        if item.is_dir() and (item / 'SKILL.md').exists():
            metadata = get_skill_metadata(item)
            if metadata:
                all_skills[item.name] = metadata

    # Resolve dependencies
    if resolve_deps:
        ordered_skills = get_dependency_order(skill_names, all_skills)
    else:
        ordered_skills = skill_names

    # Ensure Claude skills directory exists
    CLAUDE_SKILLS_DIR.mkdir(parents=True, exist_ok=True)

    installed = []
    failed = []
    skipped = []

    for skill_name in ordered_skills:
        source = SKILLS_DIR / skill_name
        destination = CLAUDE_SKILLS_DIR / skill_name

        if not source.exists():
            failed.append({'skill': skill_name, 'reason': 'Skill not found'})
            continue

        if destination.exists():
            skipped.append(skill_name)
            continue

        try:
            shutil.copytree(source, destination)
            installed.append(skill_name)
        except Exception as e:
            failed.append({'skill': skill_name, 'reason': str(e)})

    return jsonify({
        'installed': len(installed),
        'failed': len(failed),
        'skipped': len(skipped),
        'resolved_dependencies': len(ordered_skills) - len(skill_names),
        'details': {
            'installed': installed,
            'failed': failed,
            'skipped': skipped,
            'order': ordered_skills
        }
    })


@app.route('/api/uninstall', methods=['POST'])
def uninstall_skills():
    """Uninstall selected skills from Claude skills directory."""
    data = request.json
    skill_names = data.get('skills', [])

    if not skill_names:
        return jsonify({'error': 'No skills specified'}), 400

    uninstalled = []
    failed = []

    for skill_name in skill_names:
        destination = CLAUDE_SKILLS_DIR / skill_name

        if not destination.exists():
            failed.append({'skill': skill_name, 'reason': 'Skill not installed'})
            continue

        try:
            shutil.rmtree(destination)
            uninstalled.append(skill_name)
        except Exception as e:
            failed.append({'skill': skill_name, 'reason': str(e)})

    return jsonify({
        'uninstalled': len(uninstalled),
        'failed': len(failed),
        'details': {
            'uninstalled': uninstalled,
            'failed': failed
        }
    })


@app.route('/api/status', methods=['GET'])
def get_status():
    """Get installation status."""
    return jsonify({
        'claude_skills_dir': str(CLAUDE_SKILLS_DIR),
        'exists': CLAUDE_SKILLS_DIR.exists(),
        'writable': os.access(CLAUDE_SKILLS_DIR.parent, os.W_OK)
    })


@app.route('/api/search', methods=['GET'])
def search_skills():
    """Search skills by various criteria."""
    query = request.args.get('q', '').lower()
    tags = request.args.getlist('tag')
    languages = request.args.getlist('language')
    difficulty = request.args.get('difficulty')
    category = request.args.get('category')
    
    excluded_dirs = {'skill-manager', 'node_modules', 'skill-creator', 'scripts', 'template', 'pipelines', '.venv'}
    results = []

    for item in SKILLS_DIR.iterdir():
        if item.is_dir() and not item.name.startswith('.') and item.name not in excluded_dirs:
            if (item / 'SKILL.md').exists():
                metadata = get_skill_metadata(item)
                if not metadata:
                    continue
                
                # Filter by query
                if query:
                    if query not in metadata['name'].lower() and query not in metadata['description'].lower():
                        continue
                
                # Filter by tags
                if tags:
                    if not any(tag in metadata['tags'] for tag in tags):
                        continue
                
                # Filter by languages
                if languages:
                    if not any(lang in metadata['languages'] for lang in languages):
                        continue
                
                # Filter by difficulty
                if difficulty and metadata['difficulty'] != difficulty:
                    continue
                
                skill_data = {
                    'name': item.name,
                    'description': metadata['description'],
                    'version': metadata['version'],
                    'tags': metadata['tags'],
                    'difficulty': metadata['difficulty'],
                    'languages': metadata['languages'],
                    'dependencies': metadata['dependencies'],
                    'installed': is_skill_installed(item.name),
                }
                skill_data['category'] = get_skill_category(skill_data)
                
                # Filter by category
                if category and skill_data['category'] != category:
                    continue
                
                results.append(skill_data)

    return jsonify({
        'skills': sorted(results, key=lambda x: x['name']),
        'total': len(results)
    })


@app.route('/api/dependencies/<skill_name>', methods=['GET'])
def get_dependencies(skill_name: str):
    """Get dependency tree for a skill."""
    skill_path = SKILLS_DIR / skill_name
    
    if not skill_path.exists():
        return jsonify({'error': 'Skill not found'}), 404
    
    metadata = get_skill_metadata(skill_path)
    if not metadata:
        return jsonify({'error': 'Invalid skill'}), 400
    
    def build_tree(name: str, visited: Optional[Set[str]] = None) -> Dict:
        if visited is None:
            visited = set()
        
        if name in visited:
            return {'name': name, 'circular': True}
        
        visited.add(name)
        
        skill_meta = get_skill_metadata(SKILLS_DIR / name)
        if not skill_meta:
            return {'name': name, 'error': 'Not found'}
        
        deps = []
        for dep in skill_meta.get('dependencies', []):
            deps.append(build_tree(dep, visited.copy()))
        
        return {
            'name': name,
            'description': skill_meta['description'],
            'installed': is_skill_installed(name),
            'dependencies': deps
        }
    
    return jsonify(build_tree(skill_name))


if __name__ == '__main__':
    print(f"Repository root: {REPO_ROOT}")
    print(f"Claude skills directory: {CLAUDE_SKILLS_DIR}")
    print(f"Starting server on http://localhost:8080")
    app.run(debug=True, port=8080)
