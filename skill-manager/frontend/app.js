// API endpoint
const API_BASE = 'http://localhost:8080/api';

// State
let allSkills = [];
let selectedSkills = new Set();
let currentCategory = 'all';
let currentTag = null;
let currentLanguage = null;
let currentDifficulty = null;
let allTags = [];
let allLanguages = [];
let categories = [];

// Initialize
document.addEventListener('DOMContentLoaded', () => {
    loadSkills();
    setupEventListeners();
});

// Setup event listeners
function setupEventListeners() {
    const installAllBtn = document.getElementById('installAll');
    const installSelectedBtn = document.getElementById('installSelected');
    const refreshBtn = document.getElementById('refresh');
    const searchInput = document.getElementById('searchInput');
    const helpBtn = document.getElementById('helpBtn');

    if (installAllBtn) installAllBtn.addEventListener('click', installAllSkills);
    if (installSelectedBtn) installSelectedBtn.addEventListener('click', installSelectedSkills);
    if (refreshBtn) refreshBtn.addEventListener('click', loadSkills);
    if (searchInput) searchInput.addEventListener('input', debounce(handleSearch, 300));
    if (helpBtn) helpBtn.addEventListener('click', openHelpModal);

    // Help modal
    const modal = document.getElementById('helpModal');
    const closeBtn = document.querySelector('.close');

    if (closeBtn) closeBtn.addEventListener('click', closeHelpModal);

    window.addEventListener('click', (e) => {
        if (e.target === modal) {
            closeHelpModal();
        }
    });

    // Filter tabs
    document.querySelectorAll('.tab').forEach(tab => {
        tab.addEventListener('click', () => {
            document.querySelectorAll('.tab').forEach(t => t.classList.remove('active'));
            tab.classList.add('active');
            currentCategory = tab.dataset.category;
            renderSkills();
        });
    });
}

// Debounce function
function debounce(func, wait) {
    let timeout;
    return function executedFunction(...args) {
        const later = () => {
            clearTimeout(timeout);
            func(...args);
        };
        clearTimeout(timeout);
        timeout = setTimeout(later, wait);
    };
}

// Load skills from API
async function loadSkills() {
    try {
        const response = await fetch(`${API_BASE}/skills`);
        if (!response.ok) throw new Error('Failed to load skills');

        const data = await response.json();
        allSkills = data.skills;
        allTags = data.tags || [];
        allLanguages = data.languages || [];
        categories = data.categories || [];
        
        renderFilterOptions();
        renderSkills();
        updateStats();
    } catch (error) {
        console.error('Error loading skills:', error);
        showNotification('Failed to load skills. Make sure the backend server is running.', 'error');
        document.getElementById('skillsList').innerHTML = `
            <div class="loading">
                ❌ Failed to load skills<br>
                <small>Make sure the backend server is running on port 8080</small>
            </div>
        `;
    }
}

// Render filter options
function renderFilterOptions() {
    // Render tags
    const tagsContainer = document.getElementById('tagsFilter');
    if (tagsContainer && allTags.length > 0) {
        tagsContainer.innerHTML = `
            <select id="tagSelect" class="filter-select">
                <option value="">All Tags</option>
                ${allTags.map(tag => `<option value="${tag}">${tag}</option>`).join('')}
            </select>
        `;
        document.getElementById('tagSelect').addEventListener('change', (e) => {
            currentTag = e.target.value || null;
            renderSkills();
        });
    }
    
    // Render languages
    const langsContainer = document.getElementById('langsFilter');
    if (langsContainer && allLanguages.length > 0) {
        langsContainer.innerHTML = `
            <select id="langSelect" class="filter-select">
                <option value="">All Languages</option>
                ${allLanguages.map(lang => `<option value="${lang}">${lang}</option>`).join('')}
            </select>
        `;
        document.getElementById('langSelect').addEventListener('change', (e) => {
            currentLanguage = e.target.value || null;
            renderSkills();
        });
    }
    
    // Render difficulty
    const diffContainer = document.getElementById('diffFilter');
    if (diffContainer) {
        diffContainer.innerHTML = `
            <select id="diffSelect" class="filter-select">
                <option value="">All Difficulties</option>
                <option value="beginner">Beginner</option>
                <option value="intermediate">Intermediate</option>
                <option value="advanced">Advanced</option>
            </select>
        `;
        document.getElementById('diffSelect').addEventListener('change', (e) => {
            currentDifficulty = e.target.value || null;
            renderSkills();
        });
    }
}

// Render skills
function renderSkills() {
    const container = document.getElementById('skillsList');
    const searchTerm = document.getElementById('searchInput').value.toLowerCase();

    let filteredSkills = allSkills.filter(skill => {
        // Search filter
        const matchesSearch = skill.name.toLowerCase().includes(searchTerm) ||
                            skill.description.toLowerCase().includes(searchTerm) ||
                            (skill.tags && skill.tags.some(t => t.toLowerCase().includes(searchTerm)));

        // Installed filter
        if (currentCategory === 'installed') {
            return matchesSearch && skill.installed;
        }
        
        // Category filter
        const matchesCategory = currentCategory === 'all' || skill.category === currentCategory;
        
        // Tag filter
        const matchesTag = !currentTag || (skill.tags && skill.tags.includes(currentTag));
        
        // Language filter
        const matchesLang = !currentLanguage || (skill.languages && skill.languages.includes(currentLanguage));
        
        // Difficulty filter
        const matchesDiff = !currentDifficulty || skill.difficulty === currentDifficulty;

        return matchesSearch && matchesCategory && matchesTag && matchesLang && matchesDiff;
    });

    if (filteredSkills.length === 0) {
        container.innerHTML = '<div class="loading">No skills found matching criteria</div>';
        return;
    }

    container.innerHTML = filteredSkills.map(skill => createSkillCard(skill)).join('');

    // Add click handlers
    document.querySelectorAll('.skill-card').forEach(card => {
        card.addEventListener('click', (e) => {
            if (e.target.type !== 'checkbox' && !e.target.classList.contains('skill-tag')) {
                const checkbox = card.querySelector('.skill-checkbox');
                if (checkbox && !checkbox.disabled) {
                    checkbox.checked = !checkbox.checked;
                    handleSkillSelection(checkbox);
                }
            }
        });

        const checkbox = card.querySelector('.skill-checkbox');
        if (checkbox) {
            checkbox.addEventListener('change', (e) => {
                e.stopPropagation();
                handleSkillSelection(checkbox);
            });
        }
        
        // View dependencies button
        const depsBtn = card.querySelector('.view-deps');
        if (depsBtn) {
            depsBtn.addEventListener('click', (e) => {
                e.stopPropagation();
                viewDependencies(depsBtn.dataset.skill);
            });
        }
    });
}

// Create skill card HTML
function createSkillCard(skill) {
    const isSelected = selectedSkills.has(skill.name);
    const categoryLabel = formatCategory(skill.category);
    const difficultyClass = `diff-${skill.difficulty}`;
    const tagsHtml = skill.tags && skill.tags.length > 0 
        ? skill.tags.slice(0, 3).map(t => `<span class="skill-tag">${t}</span>`).join('') 
        : '';
    const depsBtn = skill.dependencies && skill.dependencies.length > 0
        ? `<button class="view-deps" data-skill="${skill.name}">🔗 ${skill.dependencies.length} deps</button>`
        : '';

    return `
        <div class="skill-card ${isSelected ? 'selected' : ''} ${skill.installed ? 'installed' : ''}"
             data-skill="${skill.name}">
            <div class="skill-header">
                <div class="skill-name">${formatSkillName(skill.name)}</div>
                <input type="checkbox" class="skill-checkbox"
                       ${isSelected ? 'checked' : ''}
                       ${skill.installed ? 'disabled' : ''}>
            </div>
            <div class="skill-meta">
                <span class="skill-category cat-${skill.category}">${categoryLabel}</span>
                <span class="skill-difficulty ${difficultyClass}">${skill.difficulty}</span>
                ${depsBtn}
            </div>
            <div class="skill-description">${skill.description}</div>
            <div class="skill-tags">${tagsHtml}</div>
            <span class="skill-status ${skill.installed ? 'status-installed' : 'status-available'}">
                ${skill.installed ? '✓ Installed' : '○ Available'}
            </span>
        </div>
    `;
}

// Format category name
function formatCategory(category) {
    return category.split('-').map(w => w.charAt(0).toUpperCase() + w.slice(1)).join(' ');
}

// Format skill name
function formatSkillName(name) {
    return name.split('-')
        .map(word => word.charAt(0).toUpperCase() + word.slice(1))
        .join(' ');
}

// Handle skill selection
function handleSkillSelection(checkbox) {
    const card = checkbox.closest('.skill-card');
    const skillName = card.dataset.skill;

    if (checkbox.checked) {
        selectedSkills.add(skillName);
        card.classList.add('selected');
    } else {
        selectedSkills.delete(skillName);
        card.classList.remove('selected');
    }

    updateStats();
}

// Handle search
function handleSearch() {
    renderSkills();
}

// Update stats
function updateStats() {
    const installedCount = allSkills.filter(s => s.installed).length;
    const availableCount = allSkills.length - installedCount;

    document.getElementById('totalSkills').textContent =
        `${allSkills.length} skills (${installedCount} installed, ${availableCount} available)`;
    document.getElementById('selectedCount').textContent = `${selectedSkills.size} selected`;
}

// View dependencies
async function viewDependencies(skillName) {
    try {
        const response = await fetch(`${API_BASE}/dependencies/${skillName}`);
        if (!response.ok) throw new Error('Failed to load dependencies');
        
        const data = await response.json();
        showDependenciesModal(skillName, data);
    } catch (error) {
        console.error('Error loading dependencies:', error);
        showNotification('Failed to load dependencies', 'error');
    }
}

// Show dependencies modal
function showDependenciesModal(skillName, depTree) {
    const modal = document.getElementById('depsModal');
    const content = document.getElementById('depsContent');
    
    const renderTree = (node, indent = 0) => {
        const prefix = '  '.repeat(indent);
        const status = node.installed ? '✓' : '○';
        let html = `<div class="dep-node">${prefix}${status} ${node.name}`;
        if (node.description) {
            html += `<br>${prefix}  <small>${node.description}</small>`;
        }
        if (node.dependencies && node.dependencies.length > 0) {
            html += `<br>${prefix}  └──`;
            for (const dep of node.dependencies) {
                html += renderTree(dep, indent + 1);
            }
        }
        html += '</div>';
        return html;
    };
    
    content.innerHTML = `
        <h3>Dependencies for ${formatSkillName(skillName)}</h3>
        <div class="dep-tree">
            ${renderTree(depTree)}
        </div>
    `;
    
    modal.classList.add('show');
    document.body.style.overflow = 'hidden';
}

// Install all skills
async function installAllSkills() {
    const availableSkills = allSkills.filter(s => !s.installed).map(s => s.name);

    if (availableSkills.length === 0) {
        showNotification('All skills are already installed!', 'info');
        return;
    }

    if (!confirm(`Install ${availableSkills.length} skills? Dependencies will be resolved automatically.`)) {
        return;
    }

    await installSkills(availableSkills, true);
}

// Install selected skills
async function installSelectedSkills() {
    if (selectedSkills.size === 0) {
        showNotification('Please select at least one skill to install', 'info');
        return;
    }

    if (!confirm(`Install ${selectedSkills.size} selected skill(s)? Dependencies will be resolved automatically.`)) {
        return;
    }

    await installSkills(Array.from(selectedSkills), true);
}

// Install skills
async function installSkills(skillNames, resolveDeps = true) {
    try {
        showNotification('Installing skills...', 'info');

        const response = await fetch(`${API_BASE}/install`, {
            method: 'POST',
            headers: {
                'Content-Type': 'application/json',
            },
            body: JSON.stringify({ 
                skills: skillNames,
                resolveDependencies: resolveDeps
            })
        });

        if (!response.ok) throw new Error('Installation failed');

        const result = await response.json();
        
        let message = `Successfully installed ${result.installed} skill(s)!`;
        if (result.resolved_dependencies > 0) {
            message += ` (${result.resolved_dependencies} dependencies resolved)`;
        }
        if (result.skipped > 0) {
            message += ` ${result.skipped} already installed.`;
        }
        
        showNotification(message, 'success');

        selectedSkills.clear();
        loadSkills();

    } catch (error) {
        console.error('Error installing skills:', error);
        showNotification('Failed to install skills. Please try again.', 'error');
    }
}

// Show notification
function showNotification(message, type = 'info') {
    const notification = document.getElementById('notification');
    notification.textContent = message;
    notification.className = `notification ${type} show`;

    setTimeout(() => {
        notification.classList.remove('show');
    }, 4000);
}

// Help modal functions
function openHelpModal() {
    const modal = document.getElementById('helpModal');
    modal.classList.add('show');
    document.body.style.overflow = 'hidden';
}

function closeHelpModal() {
    const modal = document.getElementById('helpModal');
    modal.classList.remove('show');
    document.body.style.overflow = 'auto';
}

// Language toggle
let currentLang = 'zh'; // Default to Chinese

function toggleLanguage() {
    const zhContent = document.getElementById('helpContentZh');
    const enContent = document.getElementById('helpContentEn');
    const langToggle = document.getElementById('langToggle');
    const helpTitle = document.getElementById('helpTitle');

    if (currentLang === 'zh') {
        // Switch to English
        zhContent.style.display = 'none';
        enContent.style.display = 'block';
        langToggle.textContent = '中文';
        helpTitle.textContent = '📖 How to Use Skills';
        currentLang = 'en';
    } else {
        // Switch to Chinese
        zhContent.style.display = 'block';
        enContent.style.display = 'none';
        langToggle.textContent = 'EN';
        helpTitle.textContent = '📖 如何使用 Skills';
        currentLang = 'zh';
    }
}

// Add language toggle event listener
document.addEventListener('DOMContentLoaded', () => {
    const langToggleBtn = document.getElementById('langToggle');
    if (langToggleBtn) {
        langToggleBtn.addEventListener('click', toggleLanguage);
    }
});

// Keyboard shortcut for help (? key)
document.addEventListener('keydown', (e) => {
    if (e.key === '?' && !e.ctrlKey && !e.metaKey && !e.altKey) {
        const modal = document.getElementById('helpModal');
        if (modal.classList.contains('show')) {
            closeHelpModal();
        } else {
            openHelpModal();
        }
    }
    // ESC to close modals
    if (e.key === 'Escape') {
        closeHelpModal();
        const depsModal = document.getElementById('depsModal');
        if (depsModal) {
            depsModal.classList.remove('show');
            document.body.style.overflow = 'auto';
        }
    }
});
