"""TCIH: Typed Contextual Inference Hypergraphs (corrected reference core).

A self-contained, dependency-free implementation of the formal model and
algorithms of the accompanying paper. Public API re-exported here for
convenience.
"""
from __future__ import annotations

from .formula import (And, Atom, BOT, Bot, Formula, Imp, Not, Or, apply_subst,
                      imp, land, lor, match, neg, parse)
from .model import (Builder, Context, Event, TCIH, Vertex, ctx, dom, lookup,
                    restrict, show_ctx, union_consistent)
from .rules import LIBRARY, RuleSchema, classical, intuitionistic
from .check import CheckResult, Issue, structural_check

__all__ = [
    "Formula", "Atom", "Not", "And", "Or", "Imp", "Bot", "BOT",
    "parse", "neg", "land", "lor", "imp", "apply_subst", "match",
    "Vertex", "Event", "TCIH", "Builder", "Context", "ctx", "dom", "lookup",
    "restrict", "show_ctx", "union_consistent",
    "LIBRARY", "RuleSchema", "intuitionistic", "classical",
    "structural_check", "CheckResult", "Issue",
]

__version__ = "2.0.0"
