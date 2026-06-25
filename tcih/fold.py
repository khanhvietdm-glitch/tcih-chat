"""Folding of TCIHs and the corrected quotient-acyclicity criterion.

Two repairs from the editorial review are implemented and demonstrated here:

  * Issue 4.7 -- Proposition 4.6.1 (``a quotient is a DAG whenever each class is
    an antichain'') is FALSE. `antichain_counterexample()` reproduces the
    reviewer's witness a1->b1, b2->a2 with classes {a1,a2},{b1,b2}: each class
    is an antichain yet the quotient has a 2-cycle. The correct sufficient
    condition is a RANK function (`rank_certifies_acyclic`).

  * Issues 4.4 / 4.8 -- content-only folding is unsound; label- (context-)
    preserving folding is sound. `content_only_fold` vs `context_preserving_fold`
    on `gallery.bad_fold_base` exhibit exactly this: the former produces a graph
    that `structural_check` rejects; the latter leaves a well-formed graph and,
    where judgments genuinely repeat, soundly shares them.
"""
from __future__ import annotations

from collections import defaultdict
from typing import Dict, List, Set, Tuple

from .formula import And, Atom, Imp
from .model import Builder, Event, TCIH, Vertex


# --------------------------------------------------------------------------- #
# Generic quotient
# --------------------------------------------------------------------------- #
def quotient(g: TCIH, rep: Dict[str, str]) -> TCIH:
    """Fold g by the vertex map `rep` (vid -> representative vid).

    Sources and targets are remapped to representatives; structurally identical
    events are de-duplicated; each surviving event keeps its rule, substitution,
    discharge set and provenance (order- and label-preserving fold)."""
    out = TCIH()
    for vid, rrep in rep.items():
        if rrep not in out.vertices:
            out.vertices[rrep] = Vertex(rrep, g.vertices[rrep].gamma,
                                        g.vertices[rrep].phi, g.vertices[rrep].tau)
    seen: Set[Tuple] = set()
    for e in g.events:
        src = tuple(rep[s] for s in e.sources)
        tgt = rep[e.target]
        key = (e.rule, tuple(sorted(src)), tgt, e.sigma, tuple(sorted(e.discharged)), e.prov)
        if key in seen:
            continue
        seen.add(key)
        out.events.append(Event(e.eid, src, tgt, e.rule, e.sigma, e.discharged, e.prov))
    return out


def _classes_to_rep(classes: List[List[str]]) -> Dict[str, str]:
    rep: Dict[str, str] = {}
    for cls in classes:
        r = cls[0]
        for v in cls:
            rep[v] = r
    return rep


def context_preserving_fold(g: TCIH) -> TCIH:
    """Merge vertices with identical label (Γ, φ, τ) -- ids and discharge data
    preserved. Sound (paper, Order- and Context-Preserving Folding Theorem)."""
    by_label: Dict[Tuple, List[str]] = defaultdict(list)
    for v in g.vertices.values():
        by_label[v.label].append(v.vid)
    return quotient(g, _classes_to_rep(list(by_label.values())))


def content_only_fold(g: TCIH) -> TCIH:
    """Merge vertices with identical *content* φ, ignoring the labelled context.
    Unsound in the presence of discharge (review issue 4.4)."""
    by_phi: Dict = defaultdict(list)
    for v in g.vertices.values():
        by_phi[v.phi].append(v.vid)
    return quotient(g, _classes_to_rep(list(by_phi.values())))


# --------------------------------------------------------------------------- #
# Rank certificate for quotient acyclicity (the corrected Proposition)
# --------------------------------------------------------------------------- #
def vertex_rank(g: TCIH) -> Dict[str, int]:
    """ρ(v) = length of the longest event-chain ending at v (a rank function on
    the occurrence DAG)."""
    adj: Dict[str, List[str]] = {v: [] for v in g.vertices}
    indeg: Dict[str, int] = {v: 0 for v in g.vertices}
    for e in g.events:
        for s in e.sources:
            adj[s].append(e.target)
            indeg[e.target] += 1
    rank = {v: 0 for v in g.vertices}
    queue = [v for v in g.vertices if indeg[v] == 0]
    order: List[str] = []
    indeg2 = dict(indeg)
    while queue:
        u = queue.pop()
        order.append(u)
        for w in adj[u]:
            rank[w] = max(rank[w], rank[u] + 1)
            indeg2[w] -= 1
            if indeg2[w] == 0:
                queue.append(w)
    return rank


def rank_certifies_acyclic(g: TCIH, rep: Dict[str, str]) -> bool:
    """Sufficient condition (corrected Proposition): there is ρ with
    u∼v ⇒ ρ(u)=ρ(v) and every edge u→w has ρ(u)<ρ(w). If the original ρ is
    constant on classes and strictly increasing along edges, the quotient is a
    DAG."""
    rho = vertex_rank(g)
    # constant on classes
    cls_rank: Dict[str, int] = {}
    for v, r in rep.items():
        if r in cls_rank and cls_rank[r] != rho[v]:
            return False
        cls_rank[r] = rho[v]
    # strictly increasing along edges
    for e in g.events:
        for s in e.sources:
            if rho[s] >= rho[e.target]:
                return False
    return True


def is_acyclic(g: TCIH) -> bool:
    from .check import _has_cycle
    return not _has_cycle(g)


# --------------------------------------------------------------------------- #
# The reviewer's counterexample to the antichain condition (issue 4.7)
# --------------------------------------------------------------------------- #
def antichain_counterexample() -> Dict:
    """a1→b1, b2→a2 with classes A={a1,a2}, B={b1,b2}. Each class is a
    reachability antichain, yet the quotient A→B→A has a 2-cycle. Demonstrates
    that the antichain hypothesis of the old Proposition 4.6.1 is insufficient,
    while `rank` would (correctly) refuse this fold."""
    V = ["a1", "a2", "b1", "b2"]
    E = [("a1", "b1"), ("b2", "a2")]
    classes = {"a1": "A", "a2": "A", "b1": "B", "b2": "B"}

    # antichain within each class?  (no directed path between class members)
    def reach(src):
        seen, stack = set(), [src]
        while stack:
            x = stack.pop()
            for (u, w) in E:
                if u == x and w not in seen:
                    seen.add(w)
                    stack.append(w)
        return seen
    antichain = (("a2" not in reach("a1")) and ("a1" not in reach("a2"))
                 and ("b2" not in reach("b1")) and ("b1" not in reach("b2")))

    qE = {(classes[u], classes[w]) for (u, w) in E}
    quotient_has_cycle = ("A", "B") in qE and ("B", "A") in qE
    return {"V": V, "E": E, "classes": classes,
            "each_class_is_antichain": antichain,
            "quotient_edges": sorted(qE),
            "quotient_has_cycle": quotient_has_cycle}


# --------------------------------------------------------------------------- #
# A genuinely shareable derivation (positive folding example for the figure)
# --------------------------------------------------------------------------- #
def repeated_lemma() -> TCIH:
    """{A, A⇒B} ⊢ B ∧ B with B derived twice by identical sub-derivations; a
    context-preserving fold soundly shares the two B-occurrences into one."""
    A, B = Atom("A"), Atom("B")
    b = Builder()
    va = b.assume(A, aid="a")
    vh = b.assume(Imp(A, B), aid="h")
    vb1 = b.step("ImpE", [vh, va], B, sigma={"A": A, "B": B})
    vb2 = b.step("ImpE", [vh, va], B, sigma={"A": A, "B": B})
    b.step("AndI", [vb1, vb2], And(B, B), sigma={"A": B, "B": B})
    return b.build()


__all__ = ["quotient", "context_preserving_fold", "content_only_fold",
           "vertex_rank", "rank_certifies_acyclic", "is_acyclic",
           "antichain_counterexample", "repeated_lemma"]
