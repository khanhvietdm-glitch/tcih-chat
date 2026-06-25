"""Semantic edge validation: the oracle side of the complexity dichotomy.

`structural_check` (check.py) decides the *structural* half in polynomial time.
The *semantic* half -- is a rule instance actually a sound entailment? -- is
delegated, in general, to an external backend (SAT/SMT/ITP). For the
propositional fragment treated in the paper we provide an in-process oracle by
truth tables, so the reference implementation is end-to-end runnable; richer
fragments would call out to Lean/Coq/Isabelle or an SMT solver (paper, System
Architecture). This module also supplies the classical-validity test used by the
classical proof search and by error class E4 (unsound inference).
"""
from __future__ import annotations

from itertools import product
from typing import Dict, Iterable, List

from .formula import (And, Atom, Bot, Formula, Imp, Not, Or)
from .model import TCIH
from .rules import LIBRARY, RuleSchema
from .formula import apply_subst


def _eval(phi: Formula, asg: Dict[str, bool]) -> bool:
    if isinstance(phi, Bot):
        return False
    if isinstance(phi, Atom):
        return asg.get(phi.name, False)
    if isinstance(phi, Not):
        return not _eval(phi.sub, asg)
    if isinstance(phi, And):
        return _eval(phi.left, asg) and _eval(phi.right, asg)
    if isinstance(phi, Or):
        return _eval(phi.left, asg) or _eval(phi.right, asg)
    if isinstance(phi, Imp):
        return (not _eval(phi.left, asg)) or _eval(phi.right, asg)
    raise TypeError(phi)


def entails(gamma: Iterable[Formula], phi: Formula) -> bool:
    """Classical propositional entailment  Γ ⊨ φ  by exhaustive truth table."""
    gamma = list(gamma)
    atoms = sorted(set().union(*[g.atoms() for g in gamma], phi.atoms()) or set())
    for bits in product([False, True], repeat=len(atoms)):
        asg = dict(zip(atoms, bits))
        if all(_eval(g, asg) for g in gamma) and not _eval(phi, asg):
            return False
    return True


def valid(phi: Formula) -> bool:
    """Classical tautology check."""
    return entails([], phi)


def edge_sound(g: TCIH, eid: str, library: Dict[str, RuleSchema] | None = None) -> bool:
    """Semantic validity of one hyperedge: do the source contents classically
    entail the target content? (Detection of error class E4.)"""
    lib = library or LIBRARY
    e = next((x for x in g.events if x.eid == eid), None)
    if e is None or e.rule in ("Assume", "Axiom"):
        return True
    srcs = [g.vertices[s].phi for s in e.sources if s in g.vertices]
    tgt = g.vertices[e.target].phi
    return entails(srcs, tgt)


def all_edges_sound(g: TCIH, library: Dict[str, RuleSchema] | None = None) -> List[str]:
    """Return the ids of semantically unsound edges (empty list => all sound)."""
    return [e.eid for e in g.events
            if e.rule not in ("Assume", "Axiom") and not edge_sound(g, e.eid, library)]


__all__ = ["entails", "valid", "edge_sound", "all_edges_sound"]
