"""Rule-schema library for intuitionistic (and, with RAA, classical)
propositional natural deduction, in the corrected TCIH formulation.

A *rule schema* R = (Prem, Conc, Disch, Sort) acts on JUDGMENTS. Crucially,
the discharged objects are *assumptions* (identified by their formula here, and
by assumption ids in an event), not peer premises -- this is the correction
demanded by review issue 4.1. For implication introduction the single premise
is B (read off the source judgment Gamma, a:A |- B); the discharged assumption
must carry the formula A. The schema therefore records `discharges=[A]`, kept
separate from `premises=[B]`.

The structural checker (`check.py`) *verifies a supplied substitution* sigma
attached to each event rather than searching for one; the separation of
substitution verification from unification search is review issue 4.11.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, List

from .formula import And, Atom, BOT, Formula, Imp, Not, Or

A: Formula = Atom("A")
B: Formula = Atom("B")
C: Formula = Atom("C")


@dataclass(frozen=True)
class RuleSchema:
    name: str
    premises: tuple                # tuple[Formula] schema formulas (a multiset)
    conclusion: Formula            # schema formula
    discharges: tuple = ()         # tuple[Formula]: formulas that get discharged
    sort: str = "★"
    kind: str = "other"            # 'intro' | 'elim' | 'struct' | 'other'

    def is_discharging(self) -> bool:
        return len(self.discharges) > 0


def _S(name, premises, conclusion, discharges=(), kind="other") -> RuleSchema:
    return RuleSchema(name, tuple(premises), conclusion, tuple(discharges), "★", kind)


# The library R (Definition 3.5). 'Assume' and 'Axiom' are leaf events with no
# premises and are handled directly by the checker.
LIBRARY: Dict[str, RuleSchema] = {
    "Assume": _S("Assume", [], A, kind="struct"),
    "Axiom":  _S("Axiom", [], A, kind="struct"),
    # implication
    "ImpI": _S("ImpI", [B], Imp(A, B), discharges=[A], kind="intro"),
    "ImpE": _S("ImpE", [Imp(A, B), A], B, kind="elim"),          # modus ponens
    # conjunction
    "AndI": _S("AndI", [A, B], And(A, B), kind="intro"),
    "AndE1": _S("AndE1", [And(A, B)], A, kind="elim"),
    "AndE2": _S("AndE2", [And(A, B)], B, kind="elim"),
    # disjunction
    "OrI1": _S("OrI1", [A], Or(A, B), kind="intro"),
    "OrI2": _S("OrI2", [B], Or(A, B), kind="intro"),
    "OrE":  _S("OrE", [Or(A, B), C, C], C, discharges=[A, B], kind="elim"),
    # negation / falsum
    "NotI": _S("NotI", [BOT], Not(A), discharges=[A], kind="intro"),
    "NotE": _S("NotE", [A, Not(A)], BOT, kind="elim"),
    "BotE": _S("BotE", [BOT], C, kind="elim"),                   # ex falso quodlibet
    # classical reductio ad absurdum (discharges the assumption ¬A)
    "RAA":  _S("RAA", [BOT], A, discharges=[Not(A)], kind="elim"),
}

# Introduction/elimination pairs that form cut (detour) patterns (paper, 5.x).
CUT_PAIRS = [("ImpI", "ImpE"), ("AndI", "AndE1"), ("AndI", "AndE2")]

# Rules whose soundness can change the open context (discharge-sensitive).
DISCHARGE_RULES = {n for n, s in LIBRARY.items() if s.is_discharging()}

# The monotone, discharge-free fragment (paper, restricted closure result 4.6):
# rules that neither discharge nor branch on assumptions.
HORN_SAFE = {"ImpE", "AndI", "AndE1", "AndE2", "OrI1", "OrI2"}


def intuitionistic() -> Dict[str, RuleSchema]:
    return {k: v for k, v in LIBRARY.items() if k != "RAA"}


def classical() -> Dict[str, RuleSchema]:
    return dict(LIBRARY)


__all__ = ["RuleSchema", "LIBRARY", "CUT_PAIRS", "DISCHARGE_RULES",
           "HORN_SAFE", "intuitionistic", "classical", "A", "B", "C"]
