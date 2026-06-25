"""Semantic oracle for the real (computational) corpus: an SMT/CAS backend.

The complexity dichotomy (paper §5) delegates *semantic* edge validity to an
external backend. For the propositional fragment that backend is the truth-table
oracle (`oracle.py`); for the **computational corpus** — whose steps assert
arithmetic/algebraic (in)equalities such as ``5\\cdot 1 = 5`` or
``443+73+358 = 874`` — the appropriate backend is an SMT solver / CAS.

This module:
  * extracts the (in)equality claims from a step's LaTeX-ish text,
  * decides ground (variable-free) claims with **Z3** over the rationals, with a
    **SymPy** fallback for radicals/transcendentals (both are sound),
  * marks claims with free variables as *symbolic* (they need the proof context
    / assumptions, i.e. a richer query — deferred, not guessed),
  * exposes a `lean_backend` hook documenting how higher-order obligations would
    be dispatched to Lean/Coq/Isabelle (not run here).

A step is `valid` if every ground claim in it holds, `invalid` if some ground
claim is false (error class E4), `symbolic` if its only claims have free
variables, and `no_claim` if no checkable relation was found.
"""
from __future__ import annotations

import re
from typing import List, Optional, Tuple

import sympy
from sympy.parsing.sympy_parser import (parse_expr, standard_transformations,
                                        implicit_multiplication_application,
                                        convert_xor)

try:
    import z3
    _HAVE_Z3 = True
except Exception:                      # pragma: no cover
    _HAVE_Z3 = False

_TRANSFORM = standard_transformations + (implicit_multiplication_application, convert_xor)
_RELS = [(">=", ">="), ("<=", "<="), ("!=", "!="), ("=", "="), (">", ">"), ("<", "<")]


# --------------------------------------------------------------------------- #
# LaTeX-ish -> parseable arithmetic
# --------------------------------------------------------------------------- #
def _braces(s: str, i: int):
    """s[i] == '{'; return (inner_content, index_after_closing_brace)."""
    depth = 0
    j = i
    while j < len(s):
        if s[j] == "{":
            depth += 1
        elif s[j] == "}":
            depth -= 1
            if depth == 0:
                return s[i + 1:j], j + 1
        j += 1
    return s[i + 1:], len(s)


def _convert_macros(s: str) -> str:
    """Balanced-brace conversion of \\frac, \\dfrac, \\tfrac and \\sqrt (handles
    nesting such as \\frac{\\sqrt{2}}{2}), applied recursively."""
    out = []
    i, n = 0, len(s)
    while i < n:
        if s.startswith(("\\dfrac", "\\tfrac"), i) or s.startswith("\\frac", i):
            i += 6 if (s.startswith("\\dfrac", i) or s.startswith("\\tfrac", i)) else 5
            while i < n and s[i] == " ":
                i += 1
            if i < n and s[i] == "{":
                num, i = _braces(s, i)
                while i < n and s[i] == " ":
                    i += 1
                if i < n and s[i] == "{":
                    den, i = _braces(s, i)
                    out.append(f"(({_convert_macros(num)})/({_convert_macros(den)}))")
                    continue
            out.append("frac")
        elif s.startswith("\\sqrt", i):
            i += 5
            idx = None
            while i < n and s[i] == " ":
                i += 1
            if i < n and s[i] == "[":
                j = s.find("]", i)
                if j > 0:
                    idx = s[i + 1:j]; i = j + 1
            while i < n and s[i] == " ":
                i += 1
            if i < n and s[i] == "{":
                rad, i = _braces(s, i)
                rad = _convert_macros(rad)
                out.append(f"(({rad})**(1/({idx})))" if idx else f"sqrt(({rad}))")
                continue
            out.append("sqrt")
        else:
            out.append(s[i]); i += 1
    return "".join(out)


def _normalize(s: str) -> str:
    s = s.replace("\\left", "").replace("\\right", "")
    s = _convert_macros(s)                              # nested \frac / \sqrt
    s = s.replace("\\cdot", "*").replace("\\times", "*").replace("\\div", "/")
    s = s.replace("\\geq", ">=").replace("\\leq", "<=").replace("\\neq", "!=")
    s = s.replace("\\ge", ">=").replace("\\le", "<=")
    s = s.replace("≥", ">=").replace("≤", "<=").replace("≠", "!=").replace("×", "*").replace("·", "*")
    s = s.replace("\\pi", "pi")
    s = re.sub(r"\\text\s*\{[^{}]*\}", " ", s)          # drop \text{...} annotations
    s = s.replace("\\,", "").replace("\\;", "").replace("\\!", "").replace("\\ ", " ")
    s = s.replace("\\%", "/100").replace("%", "/100")   # percent = /100 (not deletion!)
    s = s.replace("\\$", "").replace("$", "")
    s = re.sub(r"(?<=\d),(?=\d\d\d)", "", s)            # thousands separators
    s = re.sub(r"\\[a-zA-Z]+", "", s)                   # drop other LaTeX commands
    s = s.replace("{", "(").replace("}", ")")
    s = re.sub(r"\s+", " ", s).strip()
    return s


def _split_relations(body: str) -> List[Tuple[str, str, str]]:
    """Split a (possibly chained) relation 'a = b = c' / 'x >= y' into adjacent
    (lhs, rhs, op) triples on the raw normalized string."""
    # tokenize on the relation operators, keeping them
    pat = re.compile(r"(>=|<=|!=|=|>|<)")
    parts = pat.split(body)
    if len(parts) < 3:
        return []
    operands = parts[0::2]
    ops = parts[1::2]
    out = []
    for i, op in enumerate(ops):
        out.append((operands[i].strip(), operands[i + 1].strip(), op))
    return out


def _to_expr(s: str):
    if not s:
        return None
    try:
        e = parse_expr(s, transformations=_TRANSFORM, evaluate=True)
    except Exception:
        return None
    # accept only scalar expressions (reject tuples/points, relationals, booleans)
    if not isinstance(e, sympy.Expr) or isinstance(e, sympy.logic.boolalg.BooleanAtom):
        return None
    return e


# --------------------------------------------------------------------------- #
# Z3 conversion (rational fragment) + decision
# --------------------------------------------------------------------------- #
def _to_z3(expr):
    """Convert a variable-free SymPy rational/polynomial expr to a Z3 real, or
    None if it uses radicals/transcendentals/symbols (sympy handles those)."""
    if not _HAVE_Z3:
        return None
    if expr.is_Integer:
        return z3.RealVal(int(expr))
    if expr.is_Rational:
        return z3.RealVal(sympy.Rational(expr).p) / z3.RealVal(sympy.Rational(expr).q)
    if expr.is_Add:
        acc = _to_z3(expr.args[0])
        if acc is None:
            return None
        for a in expr.args[1:]:
            z = _to_z3(a)
            if z is None:
                return None
            acc = acc + z
        return acc
    if expr.is_Mul:
        acc = _to_z3(expr.args[0])
        if acc is None:
            return None
        for a in expr.args[1:]:
            z = _to_z3(a)
            if z is None:
                return None
            acc = acc * z
        return acc
    if expr.is_Pow and expr.exp.is_Integer and int(expr.exp) >= 0:
        base = _to_z3(expr.base)
        if base is None:
            return None
        acc = z3.RealVal(1)
        for _ in range(int(expr.exp)):
            acc = acc * base
        return acc
    return None


def _decide(L, R, op) -> Optional[bool]:
    """Decide a ground relation. Returns True/False, or None if undecidable."""
    rel = {"=": lambda a, b: a == b, "!=": lambda a, b: a != b,
           ">": lambda a, b: a > b, "<": lambda a, b: a < b,
           ">=": lambda a, b: a >= b, "<=": lambda a, b: a <= b}[op]
    # SMT path (Z3) for the rational fragment
    zl, zr = _to_z3(L), _to_z3(R)
    if zl is not None and zr is not None and _HAVE_Z3:
        s = z3.Solver()
        s.add(z3.Not(rel(zl, zr)))
        r = s.check()
        if r == z3.unsat:
            return True
        if r == z3.sat:
            return False
    # CAS fallback (handles radicals exactly)
    try:
        d = sympy.simplify(L - R)
        if op == "=":
            return bool(d == 0)
        if op == "!=":
            return bool(d != 0)
        if not d.is_number:
            return None
        if op == ">":
            return bool(d > 0)
        if op == "<":
            return bool(d < 0)
        if op == ">=":
            return bool(d >= 0)
        if op == "<=":
            return bool(d <= 0)
    except Exception:
        return None
    return None


# --------------------------------------------------------------------------- #
# Public API
# --------------------------------------------------------------------------- #
_MATH = re.compile(r"\\\((.+?)\\\)|\\\[(.+?)\\\]|\$\$(.+?)\$\$|\$([^$]+?)\$", re.DOTALL)
# Constructs we do NOT attempt to verify arithmetically (to stay sound rather
# than risk a false positive): transcendental functions, sums/integrals,
# modular arithmetic, matrices, etc. Such claims are reported as `symbolic`.
_RISKY = re.compile(r"\\(log|ln|sin|cos|tan|sec|csc|cot|sum|int|prod|lim|binom|"
                    r"pmod|bmod|equiv|begin|matrix|vec|hat|overline|to|rightarrow|"
                    r"implies|approx|cdots|ldots|dots)(?![a-zA-Z])")


def step_claims(text: str) -> List[Tuple[str, str, str]]:
    """Extract (lhs, rhs, op) relation triples (as normalized strings) from a
    step's math blocks. Bodies using transcendental/specialized constructs are
    skipped, so the oracle never *guesses* on what it cannot soundly parse."""
    out = []
    for m in _MATH.finditer(text):
        body = next((g for g in m.groups() if g is not None), None)
        # skip transcendental/specialized claims and percent claims (where "%"
        # is ambiguous between a /100 multiplier and a result label) to remain
        # sound — such claims are deferred, not guessed.
        if not body or _RISKY.search(body) or "%" in body:
            continue
        out.extend(_split_relations(_normalize(body)))
    return out


def _is_rounding(L, R) -> bool:
    """A failed ground equality that is a small numerical near-miss (= used for
    ≈), e.g. 5000/7 = 714.29. Distinguished from a genuine arithmetic error."""
    try:
        lf, rf = float(L), float(R)
    except Exception:
        return False
    return abs(lf - rf) <= 1e-9 + 1e-2 * max(1.0, abs(rf))


def verify_step(text: str) -> str:
    """Classify a step's semantic status:
    valid | invalid | rounding | symbolic | no_claim."""
    claims = step_claims(text)
    if not claims:
        return "no_claim"
    saw_ground = False
    saw_rounding = False
    for ls, rs, op in claims:
        L, R = _to_expr(ls), _to_expr(rs)
        if L is None or R is None:
            continue
        if L.free_symbols or R.free_symbols:
            continue                    # symbolic: needs context (deferred)
        saw_ground = True
        if _decide(L, R, op) is False:
            if op == "=" and _is_rounding(L, R):
                saw_rounding = True
                continue
            return "invalid"            # a genuine ground claim is false -> E4
    if saw_rounding:
        return "rounding"
    return "valid" if saw_ground else "symbolic"


# --------------------------------------------------------------------------- #
# Contextual SMT: decide symbolic (in)equalities UNDER assumptions (Z3 / NRA)
# --------------------------------------------------------------------------- #
_REL = {"=": lambda a, b: a == b, "!=": lambda a, b: a != b,
        ">": lambda a, b: a > b, "<": lambda a, b: a < b,
        ">=": lambda a, b: a >= b, "<=": lambda a, b: a <= b}


def _z3_term(expr, env, side):
    """Convert a SymPy expr to a Z3 real term, declaring reals for free symbols
    (cached in `env`) and introducing auxiliary variables for square roots
    (constraints appended to `side`). Returns None if unconvertible."""
    if expr.is_Integer:
        return z3.RealVal(int(expr))
    if expr.is_Rational:
        return z3.RealVal(int(expr.p)) / z3.RealVal(int(expr.q))
    if expr.is_Symbol:
        if expr not in env:
            env[expr] = z3.Real(str(expr))
        return env[expr]
    if expr.is_Add or expr.is_Mul:
        acc = None
        for a in expr.args:
            z = _z3_term(a, env, side)
            if z is None:
                return None
            acc = z if acc is None else (acc + z if expr.is_Add else acc * z)
        return acc
    if expr.is_Pow:
        base = _z3_term(expr.base, env, side)
        if base is None:
            return None
        e = expr.exp
        if e.is_Integer and int(e) >= 0:
            acc = z3.RealVal(1)
            for _ in range(int(e)):
                acc = acc * base
            return acc
        if e.is_Integer and int(e) < 0:
            acc = z3.RealVal(1)
            for _ in range(-int(e)):
                acc = acc * base
            side.append(acc != 0)
            return z3.RealVal(1) / acc
        if e == sympy.Rational(1, 2):                     # sqrt(base)
            s = z3.Real(f"_sqrt{len(side)}")
            side.append(s >= 0)
            side.append(s * s == base)
            return s
    return None


def entails_smt(assumptions, L, R, op, timeout_ms: int = 2000) -> str:
    """Decide a (possibly symbolic) relation L op R under `assumptions`
    (a list of (Lexpr, Rexpr, op) SymPy triples). Returns
    valid | invalid | underdetermined | unknown."""
    if not _HAVE_Z3:
        return "unknown"
    env, side, cons = {}, [], []
    for al, ar, aop in assumptions:
        zl, zr = _z3_term(al, env, side), _z3_term(ar, env, side)
        if zl is None or zr is None:
            continue
        cons.append(_REL[aop](zl, zr))
    zl, zr = _z3_term(L, env, side), _z3_term(R, env, side)
    if zl is None or zr is None:
        return "unknown"
    claim = _REL[op](zl, zr)

    def check(extra):
        s = z3.Solver()
        s.set("timeout", timeout_ms)
        s.add(side + cons + [extra])
        return s.check()

    r_neg = check(z3.Not(claim))      # assumptions ∧ ¬claim
    r_pos = check(claim)              # assumptions ∧ claim
    if r_neg == z3.unsat and r_pos == z3.unsat:
        return "unknown"             # inconsistent assumptions
    if r_neg == z3.unsat:
        return "valid"               # assumptions ⇒ claim
    if r_pos == z3.unsat:
        return "invalid"             # assumptions ⇒ ¬claim
    if r_neg == z3.sat and r_pos == z3.sat:
        return "underdetermined"
    return "unknown"


def verify_step_ctx(text: str, assumptions) -> str:
    """Like `verify_step`, but decides symbolic claims under `assumptions` with
    Z3. Returns valid | invalid | rounding | symbolic | no_claim."""
    claims = step_claims(text)
    if not claims:
        return "no_claim"
    saw_decided = saw_rounding = saw_symbolic = False
    for ls, rs, op in claims:
        L, R = _to_expr(ls), _to_expr(rs)
        if L is None or R is None:
            continue
        if not (L.free_symbols or R.free_symbols):
            res = _decide(L, R, op)
            if res is False:
                if op == "=" and _is_rounding(L, R):
                    saw_rounding = True
                    continue
                return "invalid"
            saw_decided = True
        else:
            st = entails_smt(assumptions, L, R, op)
            if st == "invalid":
                return "invalid"
            if st == "valid":
                saw_decided = True
            else:
                saw_symbolic = True
    if saw_decided:
        return "valid"
    if saw_rounding:
        return "rounding"
    return "symbolic" if saw_symbolic else "valid"


# --------------------------------------------------------------------------- #
# Assumption extraction (for contextual SMT): relations + NL constraints
# --------------------------------------------------------------------------- #
def relations_of(text: str):
    """All parseable (L, R, op) SymPy relations in a step/problem text — both
    equalities and inequalities — usable as assumptions for contextual SMT."""
    out = []
    for ls, rs, op in step_claims(text):
        L, R = _to_expr(ls), _to_expr(rs)
        if L is not None and R is not None:
            out.append((L, R, op))
    return out


_POS = re.compile(r"\b([a-zA-Z])\b\s+(?:is|are|be|must be)\s+(?:a\s+|an\s+)?"
                  r"(?:strictly\s+)?positive|positive\s+(?:integer|number|real|value)s?\s+([a-zA-Z])\b")
_NEG = re.compile(r"\b([a-zA-Z])\b\s+(?:is|are|be|must be)\s+(?:a\s+|an\s+)?"
                  r"(?:strictly\s+)?negative|negative\s+(?:integer|number|real|value)s?\s+([a-zA-Z])\b")


def nl_constraints(text: str):
    """Lightweight natural-language constraints: 'x is positive' -> x > 0,
    'negative number y' -> y < 0. Returns SymPy relation triples."""
    out = []
    for m in _POS.finditer(text):
        v = m.group(1) or m.group(2)
        if v:
            out.append((sympy.Symbol(v), sympy.Integer(0), ">"))
    for m in _NEG.finditer(text):
        v = m.group(1) or m.group(2)
        if v:
            out.append((sympy.Symbol(v), sympy.Integer(0), "<"))
    return out


def lean_backend(obligation: str) -> str:                       # interface stub
    """Dispatch a higher-order obligation to Lean/Coq/Isabelle. Not run here
    (no toolchain); documents the interface used by the dichotomy dispatcher."""
    return "deferred:no-lean-toolchain"


__all__ = ["step_claims", "verify_step", "verify_step_ctx", "entails_smt",
           "relations_of", "nl_constraints", "lean_backend"]
