"""Granularity refinement as provenance-marked macro expansion/contraction.

Repositioned per review issue 4.9: the result is about replacing a *derived /
admissible macro-rule* r by its definition D_r in a base sub-library, with the
inserted block tagged by a provenance id. With provenance marking, expansion and
contraction are exact mutual inverses (no pattern-overlap / hygiene problems),
the length law

        |expand(G)| = |G| + k_r(G) · (|D_r| − 1)

holds exactly, and (corrected Corollary) the multiset of base rules *outside the
marked blocks* is preserved by contraction.

Concrete macro: HS (hypothetical syllogism)  A⇒B, B⇒C  ⊢  A⇒C, with the base
definition D_r = [Assume A; ⇒E; ⇒E; ⇒I]  (|D_r| = 4 events, so each expansion
adds |D_r|−1 = 3 events).
"""
from __future__ import annotations

from collections import Counter
from typing import Dict, List, Tuple

from .formula import Atom, Formula, Imp
from .model import Builder, Event, TCIH, Vertex, ctx, restrict, union_consistent
from .rules import LIBRARY, RuleSchema, _S, A, B, C

# macro-augmented library (for checking the coarse-grained graph)
HS_SCHEMA = _S("HS", [Imp(A, B), Imp(B, C)], Imp(A, C), kind="other")
MACRO_LIBRARY: Dict[str, RuleSchema] = {**LIBRARY, "HS": HS_SCHEMA}

DR_SIZE = 4  # |D_r| for HS


def chain_with_macro(k: int) -> TCIH:
    """A coarse derivation using the HS macro k times: from X0⇒X1, …, X_k⇒X_{k+1}
    derive X0⇒X_{k+1}."""
    b = Builder()
    Xs = [Atom(f"X{i}") for i in range(k + 2)]
    imps = [b.assume(Imp(Xs[i], Xs[i + 1]), aid=f"f{i}") for i in range(k + 1)]
    cur = imps[0]
    lo = 0
    for i in range(1, k + 1):
        hi = i + 1
        concl = Imp(Xs[0], Xs[hi])
        cur = b.step("HS", [cur, imps[i]], concl,
                     sigma={"A": Xs[0], "B": Xs[i], "C": Xs[hi]})
    return b.build()


def _expand_HS(out: TCIH, e: Event, g: TCIH, blk: str, fresh) -> None:
    """Replace one HS event by its base definition, targeting e's target."""
    vf, vg = e.sources                      # P⇒Q , Q⇒R
    sig = e.subst()
    P, Q, R = sig["A"], sig["B"], sig["C"]
    gf, gg = g.vertices[vf].gamma, g.vertices[vg].gamma
    base = union_consistent([gf, gg]) or frozenset()
    aid = fresh("a")
    # Assume P
    vP = fresh("v")
    out.vertices[vP] = Vertex(vP, ctx((aid, P)), P)
    out.events.append(Event(fresh("e"), (), vP, "Assume", prov=blk))
    # ⇒E : (P⇒Q), P  |- Q
    vQ = fresh("v")
    out.vertices[vQ] = Vertex(vQ, union_consistent([gf, ctx((aid, P))]), Q)
    out.events.append(Event(fresh("e"), (vf, vP), vQ, "ImpE",
                            sigma=tuple(sorted({"A": P, "B": Q}.items())), prov=blk))
    # ⇒E : (Q⇒R), Q  |- R
    vR = fresh("v")
    out.vertices[vR] = Vertex(vR, union_consistent([gg, gf, ctx((aid, P))]), R)
    out.events.append(Event(fresh("e"), (vg, vQ), vR, "ImpE",
                            sigma=tuple(sorted({"A": Q, "B": R}.items())), prov=blk))
    # ⇒I : discharge P  |- P⇒R  (reuse e.target)
    out.events.append(Event(fresh("e"), (vR,), e.target, "ImpI",
                            sigma=tuple(sorted({"A": P, "B": R}.items())),
                            discharged=frozenset({aid}), prov=blk))


def expand(g: TCIH, macro: str = "HS") -> TCIH:
    out = TCIH()
    counters = {"v": [0], "e": [0], "a": [0], "blk": [0]}

    def fresh(kind: str) -> str:
        counters[kind][0] += 1
        return f"{kind}{counters[kind][0]}_x"

    for v in g.vertices.values():
        out.vertices[v.vid] = v
    for e in g.events:
        if e.rule == macro:
            counters["blk"][0] += 1
            _expand_HS(out, e, g, f"blk{counters['blk'][0]}", fresh)
        else:
            out.events.append(e)
    return out


def contract(g: TCIH, macro: str = "HS") -> TCIH:
    """Collapse each provenance block back to a single macro event."""
    blocks: Dict[str, List[Event]] = {}
    plain: List[Event] = []
    for e in g.events:
        if e.prov:
            blocks.setdefault(e.prov, []).append(e)
        else:
            plain.append(e)
    out = TCIH()
    keep_vids = set()
    macro_events = []
    for blk, evs in blocks.items():
        impI = next(ev for ev in evs if ev.rule == "ImpI")     # final event -> target
        assume = next(ev for ev in evs if ev.rule == "Assume")
        # the two implication sources are the external (non-block) sources
        internal = {ev.target for ev in evs}
        ext_sources = [s for ev in evs for s in ev.sources if s not in internal]
        # order: (P⇒Q, Q⇒R) — first ⇒E uses P⇒Q, second uses Q⇒R
        impEs = [ev for ev in evs if ev.rule == "ImpE"]
        vf = [s for s in impEs[0].sources if s not in internal][0]
        vg = [s for s in impEs[1].sources if s not in internal][0]
        sig = dict(impEs[0].sigma)  # {A:P,B:Q}; need C from second
        sig2 = dict(impEs[1].sigma)
        P, Q, R = sig["A"], sig["B"], sig2["B"]
        macro_events.append(Event(f"m_{blk}", (vf, vg), impI.target, macro,
                                  sigma=tuple(sorted({"A": P, "B": Q, "C": R}.items()))))
    block_targets = {ev.target for evs in blocks.values() for ev in evs}
    block_internal = block_targets - {next(e for e in evs if e.rule == "ImpI").target
                                      for evs in blocks.values()}
    for v in g.vertices.values():
        if v.vid not in block_internal:
            out.vertices[v.vid] = v
    out.events.extend(plain)
    out.events.extend(macro_events)
    return out


def length_law(k: int) -> Dict:
    """Verify |expand(G)| = |G| + k·(|D_r|−1) and round-trip identity."""
    g = chain_with_macro(k)
    ge = expand(g)
    gc = contract(ge)
    from .check import structural_check
    base_outside = Counter(e.rule for e in g.events if e.rule != "HS")
    contracted_outside = Counter(e.rule for e in gc.events if e.rule != "HS")
    return {
        "k": k,
        "macro_edges": sum(1 for e in g.events if e.rule == "HS"),
        "|G|": len(g.events),
        "|expand(G)|": len(ge.events),
        "predicted": len(g.events) + k * (DR_SIZE - 1),
        "law_holds": len(ge.events) == len(g.events) + k * (DR_SIZE - 1),
        "coarse_wellformed": structural_check(g, MACRO_LIBRARY).ok,
        "expanded_wellformed": structural_check(ge, LIBRARY).ok,
        "roundtrip_edges_match": len(gc.events) == len(g.events),
        "outside_blocks_preserved": base_outside == contracted_outside,
    }


__all__ = ["chain_with_macro", "expand", "contract", "length_law",
           "MACRO_LIBRARY", "HS_SCHEMA", "DR_SIZE"]
