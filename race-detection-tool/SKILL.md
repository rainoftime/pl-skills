---
name: race-detection-tool
description: 'Detects data races in concurrent programs. Use when: (1) Debugging concurrency
  bugs, (2) Verifying thread safety, (3) Static analysis.'
version: 1.0.0
tags:
- concurrency
- race-detection
- static-analysis
- threading
difficulty: intermediate
languages:
- python
- rust
dependencies:
- alias-and-points-to-analysis
---

# Race Detection Tool

Detects data races in concurrent programs using dynamic analysis.

## When to Use

- Debugging concurrency bugs
- Verifying thread safety
- Static race detection
- Model checking concurrency

## What This Skill Does

1. **Instruments programs** - Add detection code
2. **Tracks accesses** - Record memory operations
3. **Analyzes ordering** - Happens-before analysis
4. **Reports races** - Location and conditions

## Static Detection

```python
class StaticRaceDetector:
    """Static analysis for potential races"""
    
    def analyze(self, program):
        """Analyze program for potential races"""
        
        issues = []
        
        # 1. Find shared variables
        shared_vars = self.find_shared_variables(program)
        
        # 2. Find unlock patterns
        for var in shared_vars:
            # Check if protected by lock
            if not self.is_protected_by_lock(var, program):
                # Potential race
                issues.append({
                    'type': 'potential_race',
                    'variable': var,
                    'warning': f"Unprotected shared variable {var}"
                })
            
            # Check double-checked locking
            if self.is_double_checked_lock(var, program):
                issues.append({
                    'type': 'double_checked_lock',
                    'variable': var,
                    'warning': f"Double-checked locking on {var}"
                })
        
        return issues
    
    def find_shared_variables(self, program):
        """Find variables accessed by multiple threads"""
        # Analyze program for thread creation
        # Track variable accesses
        pass
    
    def is_protected_by_lock(self, var, program):
        """Check if variable is protected by lock"""
        # Check lock/unlock pairs around accesses
        pass
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| **Happens-before** | Partial order of operations |
| **Vector clock** | Track causality per thread |
| **Lock set** | Locks protecting a location |
| **True positive** | Actual race |
| **False positive** | Reported but not a race |

## Race Patterns

- **Write-write** - Two writes
- **Read-write** - Write after read (lost update)
- **Read-write** - Read then write (read current)

## Tips

- Use Happens-Before for accuracy
- Consider false positives
- Profile overhead
- Use for testing, not production

## Related Skills

- `software-transactional-memory` - STM concurrency
- `actor-model-implementer` - Actor model
- `race-detection-tool` - HB analysis

## Research Tools & Artifacts

Race detection tools:

| Tool | What to Learn |
|------|---------------|
| **ThreadSanitizer** | Dynamic detection |
| **Helgrind** | Valgrind tool |

## Research Frontiers

### 1. Hybrid Detection
- **Approach**: Combine static and dynamic

## Implementation Pitfalls

| Pitfall | Real Consequence | Solution |
|---------|-----------------|----------|
| **False positives** | Noise | Refine analysis |
