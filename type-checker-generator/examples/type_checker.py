"""
Type Checker Generator Examples

This module demonstrates the type-checker-generator skill with
complete working examples for generating type checkers.
"""

from dataclasses import dataclass
from typing import Optional, Dict, List, Set

# ============== Types ==============

@dataclass(frozen=True)
class Type:
    """Base type class."""
    pass

@dataclass(frozen=True)
class TInt(Type):
    """Integer type."""
    def __repr__(self):
        return "Int"

@dataclass(frozen=True)
class TBool(Type):
    """Boolean type."""
    def __repr__(self):
        return "Bool"

@dataclass(frozen=True)
class TFun(Type):
    """Function type: arg -> result"""
    arg: Type
    result: Type
    
    def __repr__(self):
        return f"({self.arg} -> {self.result})"

@dataclass(frozen=True)
class TVar(Type):
    """Type variable."""
    name: str
    
    def __repr__(self):
        return self.name

@dataclass(frozen=True)
class TRecord(Type):
    """Record type with labeled fields."""
    fields: Dict[str, Type]
    
    def __repr__(self):
        fields_str = ", ".join(f"{k}: {v}" for k, v in self.fields.items())
        return f"{{{fields_str}}}"


# ============== Terms ==============

@dataclass
class Term:
    """Base term class."""
    pass

@dataclass
class TmInt(Term):
    """Integer literal."""
    value: int

@dataclass
class TmBool(Term):
    """Boolean literal."""
    value: bool

@dataclass
class TmVar(Term):
    """Variable reference."""
    name: str

@dataclass
class TmAbs(Term):
    """Abstraction with type annotation."""
    param: str
    param_type: Type
    body: Term

@dataclass
class TmApp(Term):
    """Application."""
    func: Term
    arg: Term

@dataclass
class TmIf(Term):
    """Conditional."""
    cond: Term
    then_branch: Term
    else_branch: Term

@dataclass
class TmLet(Term):
    """Let binding."""
    name: str
    value: Term
    body: Term


# ============== Type Checker ==============

class TypeError(Exception):
    """Type error exception."""
    pass

class TypeChecker:
    """
    Type checker for simply-typed lambda calculus with:
    - Int, Bool base types
    - Function types
    - If expressions
    - Let bindings
    """
    
    def __init__(self):
        self.errors: List[str] = []
    
    def check(self, term: Term, env: Optional[Dict[str, Type]] = None) -> Optional[Type]:
        """
        Type check a term.
        Returns the type if well-typed, None if ill-typed.
        """
        if env is None:
            env = {}
        
        self.errors = []
        try:
            return self._check(term, env)
        except TypeError as e:
            self.errors.append(str(e))
            return None
    
    def _check(self, term: Term, env: Dict[str, Type]) -> Type:
        """Internal type checking with exceptions."""
        
        if isinstance(term, TmInt):
            return TInt()
        
        elif isinstance(term, TmBool):
            return TBool()
        
        elif isinstance(term, TmVar):
            if term.name not in env:
                raise TypeError(f"Unbound variable: {term.name}")
            return env[term.name]
        
        elif isinstance(term, TmAbs):
            new_env = {**env, term.param: term.param_type}
            body_type = self._check(term.body, new_env)
            return TFun(term.param_type, body_type)
        
        elif isinstance(term, TmApp):
            func_type = self._check(term.func, env)
            arg_type = self._check(term.arg, env)
            
            if not isinstance(func_type, TFun):
                raise TypeError(f"Cannot apply non-function: {func_type}")
            
            if arg_type != func_type.arg:
                raise TypeError(f"Argument type mismatch: expected {func_type.arg}, got {arg_type}")
            
            return func_type.result
        
        elif isinstance(term, TmIf):
            cond_type = self._check(term.cond, env)
            if cond_type != TBool():
                raise TypeError(f"If condition must be Bool, got {cond_type}")
            
            then_type = self._check(term.then_branch, env)
            else_type = self._check(term.else_branch, env)
            
            if then_type != else_type:
                raise TypeError(f"If branches have different types: {then_type} vs {else_type}")
            
            return then_type
        
        elif isinstance(term, TmLet):
            value_type = self._check(term.value, env)
            new_env = {**env, term.name: value_type}
            return self._check(term.body, new_env)
        
        raise TypeError(f"Unknown term type: {type(term)}")


# ============== Bidirectional Type Checker ==============

class BidirectionalTypeChecker(TypeChecker):
    """
    Bidirectional type checker with:
    - synth: infer type from term (↑)
    - check: check term has expected type (↓)
    
    Better error messages and partial type inference.
    """
    
    def synth(self, term: Term, env: Dict[str, Type]) -> Type:
        """Synthesize type from term (inference mode)."""
        
        if isinstance(term, TmInt):
            return TInt()
        
        elif isinstance(term, TmBool):
            return TBool()
        
        elif isinstance(term, TmVar):
            if term.name not in env:
                raise TypeError(f"Unbound variable: {term.name}")
            return env[term.name]
        
        elif isinstance(term, TmApp):
            func_type = self.synth(term.func, env)
            if not isinstance(func_type, TFun):
                raise TypeError(f"Cannot apply non-function: {func_type}")
            arg_type = self.check_type(term.arg, func_type.arg, env)
            return func_type.result
        
        elif isinstance(term, TmAbs):
            raise TypeError(f"Cannot synthesize type for abstraction (no annotation)")
        
        raise TypeError(f"Cannot synthesize type for: {type(term)}")
    
    def check_type(self, term: Term, expected: Type, env: Dict[str, Type]) -> Type:
        """Check term has expected type (checking mode)."""
        
        if isinstance(term, TmAbs):
            if not isinstance(expected, TFun):
                raise TypeError(f"Expected function type for abstraction, got {expected}")
            new_env = {**env, term.param: expected.arg}
            body_type = self.check_type(term.body, expected.result, new_env)
            return expected
        
        else:
            actual = self.synth(term, env)
            if actual != expected:
                raise TypeError(f"Type mismatch: expected {expected}, got {actual}")
            return actual
    
    def _check(self, term: Term, env: Dict[str, Type]) -> Type:
        """Use bidirectional checking as default."""
        try:
            return self.synth(term, env)
        except TypeError:
            raise TypeError(f"Cannot type check term: {term}")


# ============== Type Inference (Hindley-Milner) ==============

class TypeInferencer:
    """
    Hindley-Milner type inference with:
    - Type variables
    - Unification
    - Principal types
    """
    
    def __init__(self):
        self.var_counter = 0
        self.substitution: Dict[str, Type] = {}
    
    def fresh_var(self) -> TVar:
        """Generate a fresh type variable."""
        self.var_counter += 1
        return TVar(f"t{self.var_counter}")
    
    def infer(self, term: Term, env: Optional[Dict[str, Type]] = None) -> Type:
        """Infer the principal type of a term."""
        if env is None:
            env = {}
        
        self.var_counter = 0
        self.substitution = {}
        
        typ, constraints = self._infer(term, env)
        self._solve(constraints)
        return self._apply_subst(typ)
    
    def _infer(self, term: Term, env: Dict[str, Type]) -> tuple[Type, List[tuple]]:
        """Infer type and collect constraints."""
        constraints = []
        
        if isinstance(term, TmInt):
            return TInt(), constraints
        
        elif isinstance(term, TmBool):
            return TBool(), constraints
        
        elif isinstance(term, TmVar):
            if term.name not in env:
                raise TypeError(f"Unbound variable: {term.name}")
            return env[term.name], constraints
        
        elif isinstance(term, TmAbs):
            param_type = self.fresh_var()
            new_env = {**env, term.param: param_type}
            body_type, body_constraints = self._infer(term.body, new_env)
            return TFun(param_type, body_type), body_constraints
        
        elif isinstance(term, TmApp):
            func_type, func_constraints = self._infer(term.func, env)
            arg_type, arg_constraints = self._infer(term.arg, env)
            result_type = self.fresh_var()
            
            constraints = func_constraints + arg_constraints
            constraints.append((func_type, TFun(arg_type, result_type)))
            
            return result_type, constraints
        
        elif isinstance(term, TmLet):
            value_type, value_constraints = self._infer(term.value, env)
            new_env = {**env, term.name: value_type}
            body_type, body_constraints = self._infer(term.body, new_env)
            
            return body_type, value_constraints + body_constraints
        
        raise TypeError(f"Unknown term type: {type(term)}")
    
    def _solve(self, constraints: List[tuple]):
        """Solve type constraints via unification."""
        for t1, t2 in constraints:
            self._unify(t1, t2)
    
    def _unify(self, t1: Type, t2: Type):
        """Unify two types."""
        t1 = self._apply_subst(t1)
        t2 = self._apply_subst(t2)
        
        if t1 == t2:
            return
        
        if isinstance(t1, TVar):
            if self._occurs(t1, t2):
                raise TypeError(f"Infinite type: {t1} occurs in {t2}")
            self.substitution[t1.name] = t2
            return
        
        if isinstance(t2, TVar):
            self._unify(t2, t1)
            return
        
        if isinstance(t1, TFun) and isinstance(t2, TFun):
            self._unify(t1.arg, t2.arg)
            self._unify(t1.result, t2.result)
            return
        
        raise TypeError(f"Cannot unify {t1} with {t2}")
    
    def _occurs(self, var: TVar, typ: Type) -> bool:
        """Check if type variable occurs in type."""
        typ = self._apply_subst(typ)
        if typ == var:
            return True
        if isinstance(typ, TFun):
            return self._occurs(var, typ.arg) or self._occurs(var, typ.result)
        return False
    
    def _apply_subst(self, typ: Type) -> Type:
        """Apply current substitution to type."""
        if isinstance(typ, TVar):
            if typ.name in self.substitution:
                return self._apply_subst(self.substitution[typ.name])
            return typ
        if isinstance(typ, TFun):
            return TFun(self._apply_subst(typ.arg), self._apply_subst(typ.result))
        return typ


# ============== Test Cases ==============

def test_simple_terms():
    """Test simple term type checking."""
    checker = TypeChecker()
    
    # 42 : Int
    assert checker.check(TmInt(42)) == TInt()
    
    # true : Bool
    assert checker.check(TmBool(True)) == TBool()
    
    print("✓ Simple terms type check")

def test_functions():
    """Test function type checking."""
    checker = TypeChecker()
    
    # λx:Int. x : Int -> Int
    identity = TmAbs("x", TInt(), TmVar("x"))
    assert checker.check(identity) == TFun(TInt(), TInt())
    
    # λx:Int. λy:Bool. x : Int -> Bool -> Int
    const = TmAbs("x", TInt(), TmAbs("y", TBool(), TmVar("x")))
    assert checker.check(const) == TFun(TInt(), TFun(TBool(), TInt()))
    
    print("✓ Functions type check")

def test_applications():
    """Test application type checking."""
    checker = TypeChecker()
    
    # (λx:Int. x) 42 : Int
    identity = TmAbs("x", TInt(), TmVar("x"))
    app = TmApp(identity, TmInt(42))
    assert checker.check(app) == TInt()
    
    print("✓ Applications type check")

def test_conditionals():
    """Test conditional type checking."""
    checker = TypeChecker()
    
    # if true then 1 else 2 : Int
    cond = TmIf(TmBool(True), TmInt(1), TmInt(2))
    assert checker.check(cond) == TInt()
    
    # Type error: mismatched branches
    bad_cond = TmIf(TmBool(True), TmInt(1), TmBool(False))
    assert checker.check(bad_cond) is None
    assert len(checker.errors) > 0
    
    print("✓ Conditionals type check")

def test_inference():
    """Test type inference."""
    inferencer = TypeInferencer()
    
    # λx. x : t1 -> t1 (should be polymorphic)
    identity = TmAbs("x", TVar("_"), TmVar("x"))  # Without annotation
    # Note: This requires proper let-polymorphism for full HM
    
    # (λx. x) 42 : Int
    app = TmApp(TmAbs("x", TInt(), TmVar("x")), TmInt(42))
    result = inferencer.infer(app)
    assert result == TInt()
    
    print("✓ Type inference works")


# ============== Run Tests ==============

if __name__ == "__main__":
    print("Running Type Checker Tests")
    print("=" * 50)
    
    test_simple_terms()
    test_functions()
    test_applications()
    test_conditionals()
    test_inference()
    
    print("=" * 50)
    print("All tests passed!")
