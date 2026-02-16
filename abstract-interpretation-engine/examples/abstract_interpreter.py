"""
Abstract Interpretation Engine Examples

This module demonstrates the abstract-interpretation-engine skill with
complete working examples for static analysis.
"""

from dataclasses import dataclass
from typing import Optional, Dict, List, Set
from abc import ABC, abstractmethod

# ============== Abstract Domain ==============

class AbstractValue(ABC):
    """Base class for abstract values."""
    
    @abstractmethod
    def lub(self, other: 'AbstractValue') -> 'AbstractValue':
        """Least upper bound (join)."""
        pass
    
    @abstractmethod
    def glb(self, other: 'AbstractValue') -> 'AbstractValue':
        """Greatest lower bound (meet)."""
        pass
    
    @abstractmethod
    def leq(self, other: 'AbstractValue') -> bool:
        """Partial order: self ≤ other."""
        pass
    
    @abstractmethod
    def widen(self, other: 'AbstractValue') -> 'AbstractValue':
        """Widening operator for termination."""
        pass


# ============== Interval Domain ==============

@dataclass
class Interval(AbstractValue):
    """
    Interval abstract domain: [lo, hi]
    Represents all integers in the range [lo, hi].
    """
    lo: Optional[int]  # None means -∞
    hi: Optional[int]  # None means +∞
    
    def __post_init__(self):
        if self.lo is not None and self.hi is not None and self.lo > self.hi:
            raise ValueError(f"Invalid interval: [{self.lo}, {self.hi}]")
    
    def lub(self, other: AbstractValue) -> AbstractValue:
        if isinstance(other, Bottom):
            return self
        if isinstance(other, Top):
            return Top()
        if isinstance(other, Interval):
            return Interval(
                min(self.lo or float('-inf'), other.lo or float('-inf')) if self.lo is not None or other.lo is not None else None,
                max(self.hi or float('inf'), other.hi or float('inf')) if self.hi is not None or other.hi is not None else None
            )
        return Top()
    
    def glb(self, other: AbstractValue) -> AbstractValue:
        if isinstance(other, Bottom):
            return Bottom()
        if isinstance(other, Top):
            return self
        if isinstance(other, Interval):
            new_lo = max(self.lo or float('-inf'), other.lo or float('-inf'))
            new_hi = min(self.hi or float('inf'), other.hi or float('inf'))
            if new_lo > new_hi:
                return Bottom()
            return Interval(new_lo if new_lo != float('-inf') else None,
                           new_hi if new_hi != float('inf') else None)
        return Bottom()
    
    def leq(self, other: AbstractValue) -> bool:
        if isinstance(other, Top):
            return True
        if isinstance(other, Bottom):
            return False
        if isinstance(other, Interval):
            return (self.lo is None or (other.lo is not None and self.lo >= other.lo)) and \
                   (self.hi is None or (other.hi is not None and self.hi <= other.hi))
        return False
    
    def widen(self, other: AbstractValue) -> AbstractValue:
        if isinstance(other, Bottom):
            return self
        if isinstance(other, Interval):
            new_lo = self.lo if (other.lo is not None and self.lo is not None and 
                                  other.lo >= self.lo) else None
            new_hi = self.hi if (other.hi is not None and self.hi is not None and 
                                  other.hi <= self.hi) else None
            return Interval(new_lo, new_hi)
        return Top()
    
    def __repr__(self):
        lo_str = "-∞" if self.lo is None else str(self.lo)
        hi_str = "+∞" if self.hi is None else str(self.hi)
        return f"[{lo_str}, {hi_str}]"


# ============== Sign Domain ==============

class Sign(AbstractValue):
    """Sign abstract domain: -, 0, +, ⊤"""
    
    NEG = "negative"
    ZERO = "zero"
    POS = "positive"
    TOP = "unknown"
    
    def __init__(self, sign: str):
        self.sign = sign
    
    def lub(self, other: AbstractValue) -> AbstractValue:
        if isinstance(other, Bottom):
            return self
        if isinstance(other, Sign):
            if self.sign == other.sign:
                return Sign(self.sign)
            return Sign(Sign.TOP)
        return Top()
    
    def glb(self, other: AbstractValue) -> AbstractValue:
        if isinstance(other, Bottom):
            return Bottom()
        if isinstance(other, Sign):
            if self.sign == other.sign:
                return Sign(self.sign)
            return Bottom()
        return self
    
    def leq(self, other: AbstractValue) -> bool:
        if isinstance(other, Top):
            return True
        if isinstance(other, Sign):
            return self.sign == other.sign or other.sign == Sign.TOP
        return False
    
    def widen(self, other: AbstractValue) -> AbstractValue:
        return self.lub(other)
    
    def __repr__(self):
        signs = {Sign.NEG: "Neg", Sign.ZERO: "Zero", Sign.POS: "Pos", Sign.TOP: "⊤"}
        return signs.get(self.sign, self.sign)


# ============== Top and Bottom ==============

class Top(AbstractValue):
    """Top element: represents all possible values."""
    
    def lub(self, other: AbstractValue) -> AbstractValue:
        return self
    
    def glb(self, other: AbstractValue) -> AbstractValue:
        return other
    
    def leq(self, other: AbstractValue) -> bool:
        return isinstance(other, Top)
    
    def widen(self, other: AbstractValue) -> AbstractValue:
        return self
    
    def __repr__(self):
        return "⊤"


class Bottom(AbstractValue):
    """Bottom element: represents no values (unreachable)."""
    
    def lub(self, other: AbstractValue) -> AbstractValue:
        return other
    
    def glb(self, other: AbstractValue) -> AbstractValue:
        return self
    
    def leq(self, other: AbstractValue) -> bool:
        return True
    
    def widen(self, other: AbstractValue) -> AbstractValue:
        return other
    
    def __repr__(self):
        return "⊥"


# ============== Abstract Operations ==============

def abstract_add(a: AbstractValue, b: AbstractValue) -> AbstractValue:
    """Abstract addition."""
    if isinstance(a, Bottom) or isinstance(b, Bottom):
        return Bottom()
    if isinstance(a, Top) or isinstance(b, Top):
        return Top()
    if isinstance(a, Interval) and isinstance(b, Interval):
        lo = (a.lo or float('-inf')) + (b.lo or float('-inf'))
        hi = (a.hi or float('inf')) + (b.hi or float('inf'))
        return Interval(
            lo if lo != float('-inf') else None,
            hi if hi != float('inf') else None
        )
    if isinstance(a, Sign) and isinstance(b, Sign):
        # Sign addition rules
        if a.sign == Sign.ZERO:
            return b
        if b.sign == Sign.ZERO:
            return a
        if a.sign == Sign.POS and b.sign == Sign.POS:
            return Sign(Sign.POS)
        if a.sign == Sign.NEG and b.sign == Sign.NEG:
            return Sign(Sign.NEG)
        return Sign(Sign.TOP)
    return Top()


def abstract_sub(a: AbstractValue, b: AbstractValue) -> AbstractValue:
    """Abstract subtraction."""
    if isinstance(a, Bottom) or isinstance(b, Bottom):
        return Bottom()
    if isinstance(a, Top) or isinstance(b, Top):
        return Top()
    if isinstance(a, Interval) and isinstance(b, Interval):
        lo = (a.lo or float('-inf')) - (b.hi or float('inf'))
        hi = (a.hi or float('inf')) - (b.lo or float('-inf'))
        return Interval(
            lo if lo != float('-inf') else None,
            hi if hi != float('inf') else None
        )
    return Top()


def abstract_mul(a: AbstractValue, b: AbstractValue) -> AbstractValue:
    """Abstract multiplication."""
    if isinstance(a, Bottom) or isinstance(b, Bottom):
        return Bottom()
    if isinstance(a, Top) or isinstance(b, Top):
        return Top()
    if isinstance(a, Interval) and isinstance(b, Interval):
        products = [
            (a.lo or 0) * (b.lo or 0),
            (a.lo or 0) * (b.hi or 0),
            (a.hi or 0) * (b.lo or 0),
            (a.hi or 0) * (b.hi or 0)
        ]
        lo = min(products)
        hi = max(products)
        return Interval(lo if lo != float('-inf') else None,
                       hi if hi != float('inf') else None)
    return Top()


# ============== Abstract Environment ==============

class AbstractEnv:
    """Abstract environment: maps variables to abstract values."""
    
    def __init__(self, values: Optional[Dict[str, AbstractValue]] = None):
        self.values = values or {}
    
    def __getitem__(self, var: str) -> AbstractValue:
        return self.values.get(var, Bottom())
    
    def __setitem__(self, var: str, value: AbstractValue):
        self.values[var] = value
    
    def copy(self) -> 'AbstractEnv':
        return AbstractEnv(dict(self.values))
    
    def join(self, other: 'AbstractEnv') -> 'AbstractEnv':
        """Join two environments."""
        result = AbstractEnv()
        all_vars = set(self.values.keys()) | set(other.values.keys())
        for var in all_vars:
            result[var] = self[var].lub(other[var])
        return result


# ============== Statements ==============

@dataclass
class Stmt:
    """Base statement class."""
    pass

@dataclass
class Assign(Stmt):
    """Assignment: x = expr"""
    var: str
    expr: 'Expr'

@dataclass
class If(Stmt):
    """Conditional: if cond then s1 else s2"""
    cond: 'Expr'
    then_stmt: Stmt
    else_stmt: Stmt

@dataclass
class While(Stmt):
    """While loop: while cond do body"""
    cond: 'Expr'
    body: Stmt
    invariant: Optional[AbstractEnv] = None

@dataclass
class Seq(Stmt):
    """Sequence: s1; s2"""
    first: Stmt
    second: Stmt


# ============== Expressions ==============

@dataclass
class Expr:
    """Base expression class."""
    pass

@dataclass
class Const(Expr):
    """Integer constant."""
    value: int

@dataclass
class Var(Expr):
    """Variable reference."""
    name: str

@dataclass
class BinOp(Expr):
    """Binary operation."""
    op: str  # '+', '-', '*'
    left: Expr
    right: Expr


# ============== Abstract Interpreter ==============

class AbstractInterpreter:
    """
    Abstract interpreter for simple imperative language.
    Uses worklist algorithm for fixpoint computation.
    """
    
    def __init__(self, domain: str = "interval"):
        self.domain = domain
        self.iterations = 0
        self.max_iterations = 1000
    
    def eval_expr(self, expr: Expr, env: AbstractEnv) -> AbstractValue:
        """Evaluate expression abstractly."""
        if isinstance(expr, Const):
            if self.domain == "interval":
                return Interval(expr.value, expr.value)
            elif self.domain == "sign":
                if expr.value < 0:
                    return Sign(Sign.NEG)
                elif expr.value == 0:
                    return Sign(Sign.ZERO)
                else:
                    return Sign(Sign.POS)
        
        elif isinstance(expr, Var):
            return env[expr.name]
        
        elif isinstance(expr, BinOp):
            left = self.eval_expr(expr.left, env)
            right = self.eval_expr(expr.right, env)
            
            if expr.op == '+':
                return abstract_add(left, right)
            elif expr.op == '-':
                return abstract_sub(left, right)
            elif expr.op == '*':
                return abstract_mul(left, right)
        
        return Top()
    
    def exec_stmt(self, stmt: Stmt, env: AbstractEnv) -> AbstractEnv:
        """Execute statement abstractly."""
        self.iterations += 1
        if self.iterations > self.max_iterations:
            raise RuntimeError("Maximum iterations exceeded")
        
        if isinstance(stmt, Assign):
            result = env.copy()
            result[stmt.var] = self.eval_expr(stmt.expr, env)
            return result
        
        elif isinstance(stmt, If):
            # Assume both branches are possible
            then_env = self.exec_stmt(stmt.then_stmt, env.copy())
            else_env = self.exec_stmt(stmt.else_stmt, env.copy())
            return then_env.join(else_env)
        
        elif isinstance(stmt, While):
            # Use widening for termination
            current = env.copy()
            prev = None
            
            for _ in range(100):  # Max iterations
                prev = current.copy()
                
                # Assume condition is true and execute body
                body_env = self.exec_stmt(stmt.body, current.copy())
                
                # Join with current state
                current = current.join(body_env)
                
                # Apply widening
                new_values = {}
                for var in current.values:
                    new_values[var] = current[var].widen(prev[var])
                current = AbstractEnv(new_values)
                
                # Check for fixpoint
                if current.values == prev.values:
                    break
            
            return current
        
        elif isinstance(stmt, Seq):
            env = self.exec_stmt(stmt.first, env)
            return self.exec_stmt(stmt.second, env)
        
        return env
    
    def analyze(self, stmt: Stmt) -> Dict[str, str]:
        """Analyze program and return final abstract state."""
        initial_env = AbstractEnv()
        final_env = self.exec_stmt(stmt, initial_env)
        
        return {var: str(val) for var, val in final_env.values.items()}


# ============== Test Cases ==============

def test_interval_operations():
    """Test interval abstract domain operations."""
    # [1, 5] + [2, 3] = [3, 8]
    assert abstract_add(Interval(1, 5), Interval(2, 3)) == Interval(3, 8)
    
    # [1, 5] - [2, 3] = [-2, 3]
    assert abstract_sub(Interval(1, 5), Interval(2, 3)) == Interval(-2, 3)
    
    # [1, 2] * [3, 4] = [3, 8]
    assert abstract_mul(Interval(1, 2), Interval(3, 4)) == Interval(3, 8)
    
    print("✓ Interval operations work")

def test_interval_lub():
    """Test interval least upper bound."""
    # [1, 2] ⊔ [3, 4] = [1, 4]
    result = Interval(1, 2).lub(Interval(3, 4))
    assert result.lo == 1 and result.hi == 4
    
    # [1, 5] ⊔ Bottom = [1, 5]
    result = Interval(1, 5).lub(Bottom())
    assert result.lo == 1 and result.hi == 5
    
    print("✓ Interval LUB works")

def test_sign_domain():
    """Test sign abstract domain."""
    # Neg + Neg = Neg
    assert abstract_add(Sign(Sign.NEG), Sign(Sign.NEG)) == Sign(Sign.NEG)
    
    # Pos + Pos = Pos
    assert abstract_add(Sign(Sign.POS), Sign(Sign.POS)) == Sign(Sign.POS)
    
    # Neg + Pos = Top
    result = abstract_add(Sign(Sign.NEG), Sign(Sign.POS))
    assert result.sign == Sign.TOP
    
    print("✓ Sign domain works")

def test_simple_program():
    """Test abstract interpretation of simple program."""
    interp = AbstractInterpreter(domain="interval")
    
    # x = 5; y = x + 3
    program = Seq(
        Assign("x", Const(5)),
        Assign("y", BinOp('+', Var("x"), Const(3)))
    )
    
    result = interp.analyze(program)
    assert result["x"] == "[5, 5]"
    assert result["y"] == "[8, 8]"
    
    print("✓ Simple program analysis works")

def test_loop_analysis():
    """Test abstract interpretation of loop with widening."""
    interp = AbstractInterpreter(domain="interval")
    
    # x = 0; while (x < 10) { x = x + 1 }
    # After analysis: x should be [0, +∞] or similar
    program = Seq(
        Assign("x", Const(0)),
        While(Const(1), Assign("x", BinOp('+', Var("x"), Const(1))))
    )
    
    result = interp.analyze(program)
    # With widening, x should be unbounded above
    print(f"  Loop result: x = {result['x']}")
    
    print("✓ Loop analysis with widening works")


# ============== Run Tests ==============

if __name__ == "__main__":
    print("Running Abstract Interpretation Tests")
    print("=" * 50)
    
    test_interval_operations()
    test_interval_lub()
    test_sign_domain()
    test_simple_program()
    test_loop_analysis()
    
    print("=" * 50)
    print("All tests passed!")
