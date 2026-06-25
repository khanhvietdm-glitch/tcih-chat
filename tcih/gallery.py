"""Gallery of corrected case-study derivations (paper, Section 8 / Appendix).

Every derivation is constructed with the `Builder` and is *correct by
construction*; each is intended to pass `structural_check`. The gallery is the
ground truth for the figures and the regression suite, and the proof targets
for the automated prover (`prover.py`).

Highlights of the corrections:
  * `a_imp_a`      :  ⊢ A ⇒ A  -- representable now that assumption-opening is a
                     first-class event (repairs review issue 4.5).
  * `demorgan_eq*` :  ¬(A ∨ B) ⊣⊢ (¬A ∧ ¬B)  -- a genuine intuitionistic
                     equivalence, replacing the bogus "De Morgan equivalence"
                     ¬(A∧B) ⊢ ¬A∨¬B of the original §6.11 (repairs issue 4.13).
  * `bad_fold_base`:  the valid (A⇒A)∧A derivation whose content-only folding is
                     unsound (the witness for the folding theorem, issue 4.4/4.8).
"""
from __future__ import annotations

from typing import Callable, Dict, Tuple

from .formula import And, Atom, BOT, Formula, Imp, Not, Or
from .model import Builder, TCIH

P, Q, R = Atom("P"), Atom("Q"), Atom("R")
Av, Bv = Atom("A"), Atom("B")


def _sig(**kw: Formula):
    return dict(kw)


# --------------------------------------------------------------------------- #
def a_imp_a() -> TCIH:
    """⊢ A ⇒ A from the empty set of assumptions."""
    b = Builder()
    a = b.assume(Av, aid="a")                       # a:A ⊢ A
    b.step("ImpI", [a], Imp(Av, Av), discharge=["a"], sigma=_sig(A=Av, B=Av))
    return b.build()


def modus_ponens() -> TCIH:
    """{P, P⇒Q} ⊢ Q."""
    b = Builder()
    vp = b.assume(P, aid="p")
    vh = b.assume(Imp(P, Q), aid="h")
    b.step("ImpE", [vh, vp], Q, sigma=_sig(A=P, B=Q))
    return b.build()


def hypothetical_syllogism() -> TCIH:
    """{A⇒B, B⇒C} ⊢ A⇒C."""
    C = Atom("C")
    b = Builder()
    vf = b.assume(Imp(Av, Bv), aid="f")
    vg = b.assume(Imp(Bv, C), aid="g")
    va = b.assume(Av, aid="a")
    vb = b.step("ImpE", [vf, va], Bv, sigma=_sig(A=Av, B=Bv))
    vc = b.step("ImpE", [vg, vb], C, sigma=_sig(A=Bv, B=C))
    b.step("ImpI", [vc], Imp(Av, C), discharge=["a"], sigma=_sig(A=Av, B=C))
    return b.build()


def modus_tollens() -> TCIH:
    """{P⇒Q, ¬Q} ⊢ ¬P (three-step indirect proof)."""
    b = Builder()
    vf = b.assume(Imp(P, Q), aid="f")
    vg = b.assume(Not(Q), aid="g")
    va = b.assume(P, aid="a")
    vq = b.step("ImpE", [vf, va], Q, sigma=_sig(A=P, B=Q))
    vbot = b.step("NotE", [vq, vg], BOT, sigma=_sig(A=Q))
    b.step("NotI", [vbot], Not(P), discharge=["a"], sigma=_sig(A=P))
    return b.build()


def demorgan_eq_fwd() -> TCIH:
    """¬(A ∨ B) ⊢ ¬A ∧ ¬B  (intuitionistically valid)."""
    b = Builder()
    vh = b.assume(Not(Or(Av, Bv)), aid="h")
    # ¬A
    va = b.assume(Av, aid="a")
    voa = b.step("OrI1", [va], Or(Av, Bv), sigma=_sig(A=Av, B=Bv))
    vbot1 = b.step("NotE", [voa, vh], BOT, sigma=_sig(A=Or(Av, Bv)))
    vna = b.step("NotI", [vbot1], Not(Av), discharge=["a"], sigma=_sig(A=Av))
    # ¬B
    vb = b.assume(Bv, aid="b")
    vob = b.step("OrI2", [vb], Or(Av, Bv), sigma=_sig(A=Av, B=Bv))
    vbot2 = b.step("NotE", [vob, vh], BOT, sigma=_sig(A=Or(Av, Bv)))
    vnb = b.step("NotI", [vbot2], Not(Bv), discharge=["b"], sigma=_sig(A=Bv))
    # conjoin
    b.step("AndI", [vna, vnb], And(Not(Av), Not(Bv)), sigma=_sig(A=Not(Av), B=Not(Bv)))
    return b.build()


def demorgan_eq_bwd() -> TCIH:
    """¬A ∧ ¬B ⊢ ¬(A ∨ B)  (intuitionistically valid; exercises ∨E)."""
    b = Builder()
    vh = b.assume(And(Not(Av), Not(Bv)), aid="h")
    vna = b.step("AndE1", [vh], Not(Av), sigma=_sig(A=Not(Av), B=Not(Bv)))
    vnb = b.step("AndE2", [vh], Not(Bv), sigma=_sig(A=Not(Av), B=Not(Bv)))
    vd = b.assume(Or(Av, Bv), aid="d")
    va = b.assume(Av, aid="a")
    vbotA = b.step("NotE", [va, vna], BOT, sigma=_sig(A=Av))
    vb = b.assume(Bv, aid="b")
    vbotB = b.step("NotE", [vb, vnb], BOT, sigma=_sig(A=Bv))
    vbot = b.step("OrE", [vd, vbotA, vbotB], BOT,
                  discharge=["a", "b"], sigma=_sig(A=Av, B=Bv, C=BOT))
    b.step("NotI", [vbot], Not(Or(Av, Bv)), discharge=["d"], sigma=_sig(A=Or(Av, Bv)))
    return b.build()


def bad_fold_base() -> Tuple[TCIH, Tuple[str, str]]:
    """The valid derivation {A} ⊢ (A⇒A) ∧ A whose content-only folding is
    unsound. Returns the graph together with the ids of the two same-content
    vertices (outer open A, inner discharged A) that a content-only fold would
    wrongly identify."""
    b = Builder()
    v_out = b.assume(Av, aid="a_out")     # outer A, stays open
    v_in = b.assume(Av, aid="a_in")       # inner A, will be discharged
    v_imp = b.step("ImpI", [v_in], Imp(Av, Av), discharge=["a_in"], sigma=_sig(A=Av, B=Av))
    b.step("AndI", [v_imp, v_out], And(Imp(Av, Av), Av), sigma=_sig(A=Imp(Av, Av), B=Av))
    return b.build(), (v_in, v_out)


GALLERY: Dict[str, Callable[[], TCIH]] = {
    "a_imp_a": a_imp_a,
    "modus_ponens": modus_ponens,
    "hypothetical_syllogism": hypothetical_syllogism,
    "modus_tollens": modus_tollens,
    "demorgan_eq_fwd": demorgan_eq_fwd,
    "demorgan_eq_bwd": demorgan_eq_bwd,
    "bad_fold_base": lambda: bad_fold_base()[0],
}


__all__ = ["GALLERY", "a_imp_a", "modus_ponens", "hypothetical_syllogism",
           "modus_tollens", "demorgan_eq_fwd", "demorgan_eq_bwd",
           "bad_fold_base"]
