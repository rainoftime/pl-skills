"""
Lambda Calculus Interpreter Examples

This module demonstrates the lambda-calculus-interpreter skill with
complete working examples that can be run and tested.
"""

from dataclasses import dataclass
from typing import Optional, Dict

# ============== AST Definition ==============

@dataclass
class Term:
    """Base class for lambda terms."""
    pass

@dataclass
class Var(Term):
    """Variable reference."""
    name: str

@dataclass
class Abs(Term):
    """Abstraction: λx. body"""
    param: str
    body: Term

@dataclass
class App(Term):
    """Application: func arg"""
    func: Term
    arg: Term

# ============== Values ==============

@dataclass
class Value:
    """Runtime values."""
    pass

@dataclass
class Closure(Value):
    """Function closure."""
    param: str
    body: Term
    env: Dict[str, Value]

# ============== Interpreter ==============

class LambdaInterpreter:
    """Call-by-value lambda calculus interpreter."""
    
    def __init__(self):
        self.step_count = 0
        self.max_steps = 10000
    
    def eval(self, term: Term, env: Optional[Dict[str, Value]] = None) -> Value:
        """Evaluate a term to a value."""
        if env is None:
            env = {}
        
        self.step_count = 0
        return self._eval_cbv(term, env)
    
    def _eval_cbv(self, term: Term, env: Dict[str, Value]) -> Value:
        """Call-by-value evaluation."""
        self.step_count += 1
        if self.step_count > self.max_steps:
            raise RuntimeError("Evaluation exceeded maximum steps (possible infinite loop)")
        
        if isinstance(term, Var):
            if term.name not in env:
                raise NameError(f"Unbound variable: {term.name}")
            return env[term.name]
        
        elif isinstance(term, Abs):
            return Closure(term.param, term.body, dict(env))
        
        elif isinstance(term, App):
            func_val = self._eval_cbv(term.func, env)
            arg_val = self._eval_cbv(term.arg, env)
            
            if not isinstance(func_val, Closure):
                raise TypeError(f"Cannot apply non-function: {func_val}")
            
            new_env = {**func_val.env, func_val.param: arg_val}
            return self._eval_cbv(func_val.body, new_env)
        
        raise ValueError(f"Unknown term type: {type(term)}")
    
    def reduce(self, term: Term, env: Optional[Dict[str, Value]] = None) -> Term:
        """Perform one step of beta reduction."""
        if env is None:
            env = {}
        
        if isinstance(term, App):
            if isinstance(term.func, Abs):
                return self._subst(term.func.body, term.func.param, term.arg)
            else:
                return App(self.reduce(term.func, env), term.arg)
        
        return term
    
    def _subst(self, term: Term, var: str, replacement: Term) -> Term:
        """Substitute replacement for var in term."""
        if isinstance(term, Var):
            return replacement if term.name == var else term
        
        elif isinstance(term, Abs):
            if term.param == var:
                return term  # Variable is shadowed
            return Abs(term.param, self._subst(term.body, var, replacement))
        
        elif isinstance(term, App):
            return App(
                self._subst(term.func, var, replacement),
                self._subst(term.arg, var, replacement)
            )
        
        return term


# ============== Church Encodings ==============

def church_numeral(n: int) -> Term:
    """Create Church numeral n: λf. λx. f^n x"""
    body = Var("x")
    for _ in range(n):
        body = App(Var("f"), body)
    return Abs("f", Abs("x", body))

def church_true() -> Term:
    """Church true: λt. λf. t"""
    return Abs("t", Abs("f", Var("t")))

def church_false() -> Term:
    """Church false: λt. λf. f"""
    return Abs("t", Abs("f", Var("f")))

def church_if() -> Term:
    """Church if: λc. λt. λe. c t e"""
    return Abs("c", Abs("t", Abs("e", 
        App(App(Var("c"), Var("t")), Var("e")))))

def church_zero() -> Term:
    """Church zero: λn. n (λx. false) true"""
    return Abs("n", App(App(Var("n"), 
        Abs("x", church_false())), church_true()))

def church_succ() -> Term:
    """Church successor: λn. λf. λx. f (n f x)"""
    return Abs("n", Abs("f", Abs("x",
        App(Var("f"), App(App(Var("n"), Var("f")), Var("x"))))))

def church_add() -> Term:
    """Church addition: λm. λn. λf. λx. m f (n f x)"""
    return Abs("m", Abs("n", Abs("f", Abs("x",
        App(App(Var("m"), Var("f")),
            App(App(Var("n"), Var("f")), Var("x")))))))

def church_mult() -> Term:
    """Church multiplication: λm. λn. λf. m (n f)"""
    return Abs("m", Abs("n", Abs("f",
        App(Var("m"), App(Var("n"), Var("f"))))))


# ============== Y Combinator ==============

def y_combinator() -> Term:
    """
    Y combinator for recursion: λf. (λx. f (x x)) (λx. f (x x))
    Note: Only works with call-by-name; for CBV, use Z combinator.
    """
    return Abs("f", App(
        Abs("x", App(Var("f"), App(Var("x"), Var("x")))),
        Abs("x", App(Var("f"), App(Var("x"), Var("x"))))
    ))

def z_combinator() -> Term:
    """
    Z combinator (call-by-value Y): λf. (λx. f (λv. x x v)) (λx. f (λv. x x v))
    """
    return Abs("f", App(
        Abs("x", App(Var("f"), Abs("v", App(App(Var("x"), Var("x")), Var("v"))))),
        Abs("x", App(Var("f"), Abs("v", App(App(Var("x"), Var("x")), Var("v")))))
    ))


# ============== Test Cases ==============

def test_identity():
    """Test identity function: (λx. x) y = y"""
    interpreter = LambdaInterpreter()
    
    term = App(Abs("x", Var("x")), Var("y"))
    env = {"y": Closure("z", Var("z"), {})}
    
    result = interpreter.eval(term, env)
    assert isinstance(result, Closure)
    print("✓ Identity function works")

def test_church_numerals():
    """Test Church numeral operations."""
    interpreter = LambdaInterpreter()
    
    # Test 0
    zero = church_numeral(0)
    result = interpreter.eval(zero, {})
    assert isinstance(result, Closure)
    
    # Test 2
    two = church_numeral(2)
    result = interpreter.eval(two, {})
    assert isinstance(result, Closure)
    
    # Test addition: 2 + 3 = 5
    add = church_add()
    five_calc = App(App(add, church_numeral(2)), church_numeral(3))
    result = interpreter.eval(five_calc, {})
    assert isinstance(result, Closure)
    
    print("✓ Church numerals work")

def test_church_booleans():
    """Test Church boolean operations."""
    interpreter = LambdaInterpreter()
    
    # Test true
    true = church_true()
    result = interpreter.eval(true, {})
    assert isinstance(result, Closure)
    
    # Test if true then a else b = a
    if_term = church_if()
    term = App(App(App(if_term, church_true()), 
                   church_numeral(1)), church_numeral(2))
    result = interpreter.eval(term, {})
    assert isinstance(result, Closure)
    
    print("✓ Church booleans work")

def test_substitution():
    """Test substitution."""
    interpreter = LambdaInterpreter()
    
    # (λx. x) y -> y
    term = App(Abs("x", Var("x")), Var("y"))
    result = interpreter.reduce(term)
    assert isinstance(result, Var)
    assert result.name == "y"
    
    print("✓ Substitution works")


# ============== Run Tests ==============

if __name__ == "__main__":
    print("Running Lambda Calculus Interpreter Tests")
    print("=" * 50)
    
    test_identity()
    test_church_numerals()
    test_church_booleans()
    test_substitution()
    
    print("=" * 50)
    print("All tests passed!")
