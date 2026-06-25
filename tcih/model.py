"""Core data structures of the corrected TCIH model (paper, Section 3).

This module implements the redesign demanded by the editorial review:

  * A vertex is a *labelled judgment*  v = (id_v, Gamma_v |- phi_v, tau_v),
    where the open context Gamma_v : AssumptionID -> Formula is a partial map
    from assumption identifiers to formulas -- NOT a set of formula contents.
    Distinct hypotheses with the same content therefore have distinct ids and
    are never confused (this repairs review issue 4.2).

  * The proof object is an *ordered event hypergraph*
        G = (V, E, lambda_V, lambda_E, <)
    Each event (hyperedge) is
        e = (id_e, S_e, t_e, R[sigma_e], D_e, prov_e)
    with a multiset S_e of source incidences, a target t_e, a rule instance,
    a set D_e of assumption ids discharged *at this event*, and a provenance
    tag prov_e. The open/discharged status of an assumption is DERIVED from the
    event history (membership in some live context), not stored as a mutable
    vertex flag (this repairs review issues 4.1 and 4.3).

  * Every vertex is the target of exactly one event (its unique justification);
    leaves are produced by `Assume` / `Axiom` events with empty source multiset.
    This makes assumption-opening a first-class event, so that e.g. |- A => A is
    representable (this repairs review issue 4.5).

The event order < is the dependency relation: e' < e iff target(e') is a source
incidence of e. Acyclicity of this relation is checked in `check.py`.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, FrozenSet, List, Optional, Tuple

from .formula import Formula, Subst

# ---------------------------------------------------------------------------
# Labelled contexts:  Gamma : AssumptionID -> Formula
# ---------------------------------------------------------------------------

AssumptionID = str
# A context is an immutable set of (id, formula) bindings. We keep it as a
# frozenset of pairs so vertices are hashable and comparable by label.
Context = FrozenSet[Tuple[AssumptionID, Formula]]

EMPTY_CTX: Context = frozenset()


def ctx(*bindings: Tuple[AssumptionID, Formula]) -> Context:
    return frozenset(bindings)


def dom(g: Context) -> FrozenSet[AssumptionID]:
    return frozenset(a for a, _ in g)


def lookup(g: Context, a: AssumptionID) -> Optional[Formula]:
    for aid, f in g:
        if aid == a:
            return f
    return None


def union_consistent(contexts: List[Context]) -> Optional[Context]:
    """Multiset/partial-map union that fails (returns None) on a clash:
    the same assumption id bound to two different formulas."""
    acc: Dict[AssumptionID, Formula] = {}
    for g in contexts:
        for a, f in g:
            if a in acc and acc[a] != f:
                return None
            acc[a] = f
    return frozenset(acc.items())


def restrict(g: Context, remove: FrozenSet[AssumptionID]) -> Context:
    return frozenset((a, f) for (a, f) in g if a not in remove)


def show_ctx(g: Context) -> str:
    if not g:
        return "·"  # empty context
    items = sorted(((a, str(f)) for a, f in g), key=lambda t: t[0])
    return ", ".join(f"{a}:{s}" for a, s in items)


# ---------------------------------------------------------------------------
# Vertices and events
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Vertex:
    """A labelled judgment Gamma |- phi with a unique occurrence id and sort."""

    vid: str
    gamma: Context
    phi: Formula
    tau: str = "★"  # sort; ★ for ordinary propositions

    @property
    def label(self) -> Tuple[Context, Formula, str]:
        """The (context, content, sort) triple compared by label-preserving
        folding. The id is *not* part of the label."""
        return (self.gamma, self.phi, self.tau)

    def judgment(self) -> str:
        return f"{show_ctx(self.gamma)} ⊢ {self.phi}"

    def __str__(self) -> str:
        return f"{self.vid}: {self.judgment()}"


@dataclass(frozen=True)
class Event:
    """A hyperedge / inference event.

    sources    : tuple of source vertex ids (a multiset; order is irrelevant)
    target     : the produced vertex id (unique justification of that vertex)
    rule       : the rule-schema name (looked up in a RuleLibrary)
    sigma      : the substitution instantiating the schema
    discharged : assumption ids discharged at this event (D_e)
    prov       : provenance / expansion-block tag (None, or a block id)
    """

    eid: str
    sources: Tuple[str, ...]
    target: str
    rule: str
    sigma: Tuple[Tuple[str, Formula], ...] = ()
    discharged: FrozenSet[AssumptionID] = frozenset()
    prov: Optional[str] = None

    def subst(self) -> Subst:
        return dict(self.sigma)


@dataclass
class TCIH:
    """An ordered event hypergraph. Vertices keyed by id; events in build order.

    Invariant maintained by the builder: every vertex id is the target of
    exactly one event (its justification)."""

    vertices: Dict[str, Vertex] = field(default_factory=dict)
    events: List[Event] = field(default_factory=list)

    # -- accessors ----------------------------------------------------------
    def V(self) -> List[Vertex]:
        return list(self.vertices.values())

    def justification(self, vid: str) -> Optional[Event]:
        for e in self.events:
            if e.target == vid:
                return e
        return None

    def predecessors(self, e: Event) -> List[Event]:
        """Events e' with e' < e (target of e' is a source of e)."""
        srcs = set(e.sources)
        return [p for p in self.events if p.target in srcs]

    # -- input size N (paper, encoded-input-size model) ---------------------
    def input_size(self) -> int:
        """N = sum_v |lambda_V(v)| + sum_e |lambda_E(e)| + |events|.

        |lambda_V(v)| counts the formula nodes of the content plus the size of
        the labelled context; |lambda_E(e)| counts sources, discharges and the
        substitution. This is the explicit cost model requested by the review
        (issue 4.11)."""
        nv = 0
        for v in self.vertices.values():
            nv += v.phi.size() + sum(1 + f.size() for _, f in v.gamma)
        ne = 0
        for e in self.events:
            ne += 1 + len(e.sources) + len(e.discharged)
            ne += sum(f.size() for _, f in e.sigma)
        return nv + ne

    def __str__(self) -> str:
        lines = [f"TCIH  |V|={len(self.vertices)}  |E|={len(self.events)}  N={self.input_size()}"]
        for e in self.events:
            t = self.vertices[e.target]
            src = " , ".join(self.vertices[s].judgment() for s in e.sources) or "—"
            d = ("  discharge " + ",".join(sorted(e.discharged))) if e.discharged else ""
            p = f"  [{e.prov}]" if e.prov else ""
            lines.append(f"  {e.eid:>4} {e.rule:<8} {src}  ⟹  {t.judgment()}{d}{p}")
        return "\n".join(lines)


# ---------------------------------------------------------------------------
# Builder: construct derivations correct-by-construction
# ---------------------------------------------------------------------------


class Builder:
    """Convenience constructor. `assume`/`axiom` open leaves; `step` applies a
    rule, computing the target context by the activation condition

        Gamma_t = ( U_{s in S} Gamma_s )  restricted to  dom \\ D .

    The builder makes well-formed derivations; deliberately malformed graphs
    (for the folding counterexample and error-injection tests) are produced by
    post-hoc mutation in `fold.py` / `diagnose.py`."""

    def __init__(self) -> None:
        self.g = TCIH()
        self._vc = 0
        self._ec = 0
        self._ac = 0
        self._leaf_aid: Dict[str, str] = {}  # leaf vertex id -> assumption id

    def _fresh_v(self) -> str:
        self._vc += 1
        return f"v{self._vc}"

    def _fresh_e(self) -> str:
        self._ec += 1
        return f"e{self._ec}"

    def fresh_aid(self) -> str:
        self._ac += 1
        return f"a{self._ac}"

    def assume(self, phi: Formula, aid: Optional[str] = None, tau: str = "★") -> str:
        """Open a fresh hypothesis: produces the leaf  a:phi |- phi."""
        a = aid or self.fresh_aid()
        vid = self._fresh_v()
        self.g.vertices[vid] = Vertex(vid, ctx((a, phi)), phi, tau)
        self.g.events.append(Event(self._fresh_e(), (), vid, "Assume",
                                   discharged=frozenset(), prov=None))
        # remember which aid this leaf introduced
        self._leaf_aid[vid] = a
        return vid

    def axiom(self, phi: Formula, tau: str = "★") -> str:
        """Introduce an axiom / already-proved theorem:  · |- phi."""
        vid = self._fresh_v()
        self.g.vertices[vid] = Vertex(vid, EMPTY_CTX, phi, tau)
        self.g.events.append(Event(self._fresh_e(), (), vid, "Axiom"))
        return vid

    def step(self, rule: str, sources: List[str], conclusion: Formula,
             discharge: Optional[List[str]] = None, sigma: Optional[Subst] = None,
             prov: Optional[str] = None, tau: str = "★") -> str:
        D = frozenset(discharge or [])
        src_ctxs = [self.g.vertices[s].gamma for s in sources]
        u = union_consistent(src_ctxs)
        if u is None:
            raise ValueError(f"inconsistent source contexts for {rule}")
        gamma_t = restrict(u, D)
        vid = self._fresh_v()
        self.g.vertices[vid] = Vertex(vid, gamma_t, conclusion, tau)
        sig = tuple(sorted((sigma or {}).items()))
        self.g.events.append(Event(self._fresh_e(), tuple(sources), vid, rule,
                                   sigma=sig, discharged=D, prov=prov))
        return vid

    def build(self) -> TCIH:
        return self.g


__all__ = [
    "AssumptionID", "Context", "EMPTY_CTX", "ctx", "dom", "lookup",
    "union_consistent", "restrict", "show_ctx", "Vertex", "Event", "TCIH",
    "Builder",
]
