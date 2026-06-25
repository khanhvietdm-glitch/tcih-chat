"""A real Lean 4 backend for the semantic oracle (no mathlib required).

The complexity-dichotomy dispatcher (paper §5–6) delegates semantic obligations
to an external prover. This module realizes the **Lean** branch concretely: it
renders a ground arithmetic (in)equality as a Lean proposition over ``Rat`` and
discharges it with Lean's trusted kernel via ``by decide`` (trying the negation
to distinguish *refuted* from *unknown*). It needs only a core Lean toolchain
(installed via elan); mathlib is not required for the decidable fragment.

If no Lean toolchain is present, `lean_available()` is False and callers fall
back to the Z3/SymPy backend (`smt_oracle`).
"""
from __future__ import annotations

import os
import shutil
import subprocess
import tempfile
from pathlib import Path
from typing import Optional

import sympy

_LEANOP = {"=": "=", "!=": "≠", ">": ">", "<": "<", ">=": "≥", "<=": "≤"}


def _lean_exe() -> Optional[str]:
    p = shutil.which("lean")
    if p:
        return p
    cand = Path(os.path.expanduser("~/.elan/bin/lean.exe"))
    if cand.exists():
        return str(cand)
    cand = Path(os.path.expanduser("~/.elan/bin/lean"))
    return str(cand) if cand.exists() else None


def lean_available() -> bool:
    return _lean_exe() is not None


def _run(src: str, timeout: int = 60):
    exe = _lean_exe()
    if exe is None:
        return False, "no-lean"
    with tempfile.TemporaryDirectory() as d:
        f = Path(d) / "Check.lean"
        f.write_text(src, encoding="utf-8")
        try:
            r = subprocess.run([exe, str(f)], capture_output=True, text=True,
                               timeout=timeout)
        except subprocess.TimeoutExpired:
            return False, "timeout"
        return r.returncode == 0 and not r.stderr.strip(), (r.stdout + r.stderr)


def _lean_expr(e) -> Optional[str]:
    """Render a variable-free SymPy rational/polynomial expr as a Lean term."""
    if e.is_Integer:
        return f"({int(e)} : Rat)"
    if e.is_Rational:
        return f"(({int(e.p)} : Rat) / ({int(e.q)} : Rat))"
    if e.is_Add:
        parts = [_lean_expr(a) for a in e.args]
        if any(p is None for p in parts):
            return None
        return "(" + " + ".join(parts) + ")"
    if e.is_Mul:
        parts = [_lean_expr(a) for a in e.args]
        if any(p is None for p in parts):
            return None
        return "(" + " * ".join(parts) + ")"
    if e.is_Pow and e.exp.is_Integer and int(e.exp) >= 0:
        base = _lean_expr(e.base)
        if base is None:
            return None
        return "(" + " * ".join([base] * int(e.exp)) + ")" if int(e.exp) > 0 else "(1 : Rat)"
    return None


def check_arith(L, R, op: str, timeout: int = 60) -> str:
    """Decide a ground arithmetic relation with the Lean kernel:
    valid | invalid | unknown."""
    le, re = _lean_expr(L), _lean_expr(R)
    if le is None or re is None:
        return "unknown"
    prop = f"{le} {_LEANOP[op]} {re}"
    ok, _ = _run(f"example : {prop} := by decide")
    if ok:
        return "valid"
    ok_neg, _ = _run(f"example : ¬ ({prop}) := by decide")
    if ok_neg:
        return "invalid"
    return "unknown"


# --------------------------------------------------------------------------- #
# Mathlib tier: nonlinear real / higher-order obligations via nlinarith etc.
# --------------------------------------------------------------------------- #
_LEANMATH = Path(__file__).resolve().parents[1] / "leanmath"


def mathlib_available() -> bool:
    return lean_available() and (_LEANMATH / "lake-manifest.json").exists()


def prove_mathlib(decl_src: str, timeout: int = 180) -> bool:
    """Run a Lean declaration that may use Mathlib tactics (nlinarith, norm_num,
    positivity, …) inside the mathlib-enabled project via `lake env lean`.
    Returns True iff Lean accepts it."""
    exe = shutil.which("lake") or str(Path(os.path.expanduser("~/.elan/bin/lake.exe")))
    src = "import Mathlib\n" + decl_src
    tmpdir = _LEANMATH / "tmp"
    tmpdir.mkdir(exist_ok=True)
    f = tmpdir / "Probe.lean"
    f.write_text(src, encoding="utf-8")
    try:
        r = subprocess.run([exe, "env", "lean", str(f)], cwd=str(_LEANMATH),
                           capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return False
    return r.returncode == 0 and not r.stderr.strip()


def check_nonlinear(decl_src: str) -> str:
    """proved | unproved : does Lean+Mathlib accept this declaration?"""
    return "proved" if prove_mathlib(decl_src) else "unproved"


def demo_mathlib() -> dict:
    """Representative higher-order / nonlinear-real obligations that core Lean
    cannot discharge but Lean+Mathlib can (and one that is correctly refused)."""
    if not mathlib_available():
        return {"mathlib_available": False}
    goals = {
        "AM-GM x^2+y^2>=2xy": "example (x y : ℝ) : x^2 + y^2 ≥ 2*x*y := by nlinarith [sq_nonneg (x - y)]",
        "(x-1)^2>=0 expanded": "example (x : ℝ) : x^2 - 2*x + 1 ≥ 0 := by nlinarith [sq_nonneg (x - 1)]",
        "sqrt6 - sqrt2 > 0": "example : Real.sqrt 6 - Real.sqrt 2 > 0 := by\n  have h : Real.sqrt 2 < Real.sqrt 6 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)\n  linarith",
        "false: x^2>=1 (refused)": "example (x : ℝ) : x^2 ≥ 1 := by nlinarith",
    }
    out = {"mathlib_available": True}
    for name, decl in goals.items():
        out[name] = check_nonlinear(decl)
    return out


def selftest() -> dict:
    """Quick sanity check that Lean is wired correctly."""
    from sympy import Integer, Rational
    return {
        "available": lean_available(),
        "2+2=4": check_arith(Integer(2) + 2, Integer(4), "="),
        "2+2=5": check_arith(Integer(2) + 2, Integer(5), "="),
        "1/3+2/3=1": check_arith(Rational(1, 3) + Rational(2, 3), Integer(1), "="),
        "35>25": check_arith(Integer(35), Integer(25), ">"),
    }


__all__ = ["lean_available", "check_arith", "mathlib_available", "prove_mathlib",
           "check_nonlinear", "demo_mathlib", "selftest"]


if __name__ == "__main__":                                  # pragma: no cover
    import json
    print(json.dumps(selftest(), indent=2))
