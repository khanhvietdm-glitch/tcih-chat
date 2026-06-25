"""Proof diagnosis: error classification, localization, and an injection harness.

The structure of the well-formedness conditions induces a finite error taxonomy
(paper, Diagnosis section). Structural errors E1-E3 are caught by
`structural_check` in linear time; the semantic error E4 (an inference that is
well-formed but not a sound entailment) is caught by the `oracle`. Localization
returns the *earliest* failing hyperedge in event order together with its
ancestor cone -- the smallest sub-derivation that exposes the failure.

`inject` plants a single labelled error of a chosen class into a correct
derivation; it is the generator for the synthetic, ground-truth error corpus
used in the evaluation protocol.
"""
from __future__ import annotations

from dataclasses import replace
from typing import Dict, List, Optional, Set, Tuple

from .formula import And, Atom, BOT, Imp, Not
from .model import Event, TCIH, Vertex, ctx
from .rules import LIBRARY, RuleSchema, _S, A, B
from .check import structural_check
from .oracle import all_edges_sound

# Unsound schemas (formal fallacies) for E4 modelling and the corpus.
FALLACIES: Dict[str, RuleSchema] = {
    "AffirmConsequent": _S("AffirmConsequent", [Imp(A, B), B], A),
    "DenyAntecedent": _S("DenyAntecedent", [Imp(A, B), Not(A)], Not(B)),
}
EXT_LIBRARY = {**LIBRARY, **FALLACIES}


def _event_order(g: TCIH) -> List[Event]:
    """Topological order of events (predecessors first)."""
    pos = {v: i for i, v in enumerate(g.vertices)}  # builder order ~ topological
    return sorted(g.events, key=lambda e: pos.get(e.target, 0))


def _ancestor_cone(g: TCIH, eid: str) -> Tuple[Set[str], Set[str]]:
    """Vertices and events in the sub-derivation rooted at event `eid`."""
    e0 = next((e for e in g.events if e.eid == eid), None)
    if e0 is None:
        return set(), set()
    just = {e.target: e for e in g.events}
    vts: Set[str] = set()
    evs: Set[str] = set()
    stack = [e0.target]
    while stack:
        v = stack.pop()
        if v in vts:
            continue
        vts.add(v)
        e = just.get(v)
        if e:
            evs.add(e.eid)
            stack.extend(e.sources)
    return vts, evs


def diagnose(g: TCIH, library: Optional[Dict[str, RuleSchema]] = None,
             semantic: bool = True) -> Dict:
    """Full structural + semantic diagnosis with localization."""
    lib = library or EXT_LIBRARY
    res = structural_check(g, lib)
    errors: List[Dict] = []
    for iss in res.issues:
        cls = iss.code if iss.code in ("E1", "E2", "E3") else \
              ("E1" if iss.code == "E1b" else "STRUCT")
        errors.append({"class": cls, "where": iss.where, "detail": iss.message})
    if semantic:
        for eid in all_edges_sound(g, lib):
            errors.append({"class": "E4", "where": eid,
                           "detail": "inference is well-formed but not a sound entailment"})

    # localization: earliest failing event in topological order
    failing = {er["where"] for er in errors if er["where"] not in ("—",)}
    locus = None
    cone_v: Set[str] = set()
    cone_e: Set[str] = set()
    if failing:
        order = [e.eid for e in _event_order(g)]
        ranked = [eid for eid in order if eid in failing]
        if ranked:
            locus = ranked[0]
            cone_v, cone_e = _ancestor_cone(g, locus)
    return {
        "ok": not errors,
        "errors": errors,
        "classes": sorted({er["class"] for er in errors}),
        "locus_event": locus,
        "minimal_subproof_vertices": sorted(cone_v),
        "minimal_subproof_events": sorted(cone_e),
        "input_size": res.input_size,
    }


# --------------------------------------------------------------------------- #
# Error-injection harness (ground-truth corpus generator)
# --------------------------------------------------------------------------- #
def inject(g: TCIH, kind: str, seed: int = 0) -> Tuple[TCIH, Dict]:
    """Return a copy of g with one planted error of class `kind` ∈
    {E1,E2,E3,E4}, plus a label record giving the true class and locus."""
    out = TCIH(dict(g.vertices), list(g.events))
    nonleaf = [i for i, e in enumerate(out.events) if e.rule not in ("Assume", "Axiom")]
    if not nonleaf:
        return out, {"injected": None}
    idx = nonleaf[seed % len(nonleaf)]
    e = out.events[idx]
    label = {"class": kind, "locus": e.eid}

    if kind == "E1" and e.sources:                  # drop a premise
        out.events[idx] = replace(e, sources=e.sources[1:])
    elif kind == "E2":                              # corrupt the target context
        t = out.vertices[e.target]
        out.vertices[e.target] = replace(t, gamma=t.gamma | {("ghost", Atom("Z"))})
    elif kind == "E3":                              # discharge a non-open id
        out.events[idx] = replace(e, discharged=e.discharged | {"ghost"})
    elif kind == "E4":                              # swap to an unsound schema
        # find an ImpE and turn it into AffirmConsequent (B, A⇒B ⊢ A)
        for j in nonleaf:
            ej = out.events[j]
            if ej.rule == "ImpE":
                sig = ej.subst()
                Af, Bf = sig.get("A"), sig.get("B")
                if Af is not None and Bf is not None:
                    t = out.vertices[ej.target]
                    out.vertices[ej.target] = replace(t, phi=Af)   # claim A
                    out.events[j] = replace(ej, rule="AffirmConsequent")
                    label = {"class": "E4", "locus": ej.eid}
                    break
        else:
            return out, {"injected": None}
    else:
        return out, {"injected": None}
    return out, label


__all__ = ["diagnose", "inject", "FALLACIES", "EXT_LIBRARY"]
