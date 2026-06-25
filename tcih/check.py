"""StructuralCheck: polynomial-time structural well-formedness of a TCIH
(paper, Section 4 / Algorithm 1).

This is the structural half of the complexity dichotomy (review issue 4.11):
it decides well-formedness of an event hypergraph in time linear in the encoded
input size N (Definition of N in `model.TCIH.input_size`), under the standard
assumption that formula equality/hashing is O(size). It *verifies the supplied
substitution* attached to each event; it does not search for a unifier.

Semantic edge validity (review/paper E4) is delegated to `oracle.py`.
"""
from __future__ import annotations

from collections import Counter
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple

from .formula import Formula, apply_subst
from .model import TCIH, Vertex, dom, lookup, restrict, union_consistent
from .rules import LIBRARY, RuleSchema


@dataclass
class Issue:
    code: str          # structural error code, see TAXONOMY
    where: str         # event id or vertex id
    message: str

    def __str__(self) -> str:
        return f"[{self.code}] {self.where}: {self.message}"


@dataclass
class CheckResult:
    ok: bool
    issues: List[Issue] = field(default_factory=list)
    input_size: int = 0
    edges: int = 0

    def __bool__(self) -> bool:
        return self.ok

    def __str__(self) -> str:
        if self.ok:
            return f"well-formed (N={self.input_size}, |E|={self.edges})"
        return "ILL-FORMED\n  " + "\n  ".join(str(i) for i in self.issues)


# Structural taxonomy (paper Table: error taxonomy). E4 is semantic (oracle).
TAXONOMY = {
    "E1": "missing/extra premise: source multiset ≠ Prem(R[σ])",
    "E1b": "conclusion mismatch: target ≠ Conc(R[σ])",
    "E2": "wrong open context: Γ_t ≠ (⊎ Γ_s) ↾ (dom∖D)",
    "E3": "discharge without an open witness, or discharged id still open",
    "WF": "malformed leaf / unknown rule / non-unique justification",
    "ACY": "occurrence cycle: event-dependency order is not acyclic",
}


def _multiset(formulas) -> Counter:
    return Counter(formulas)


def structural_check(g: TCIH, library: Optional[Dict[str, RuleSchema]] = None) -> CheckResult:
    lib = library or LIBRARY
    issues: List[Issue] = []

    # -- 0. unique justification -------------------------------------------
    just_count: Counter = Counter(e.target for e in g.events)
    for vid in g.vertices:
        c = just_count.get(vid, 0)
        if c == 0:
            issues.append(Issue("WF", vid, "vertex has no justifying event"))
        elif c > 1:
            issues.append(Issue("WF", vid, f"vertex has {c} justifications (must be 1)"))

    # -- 1. per-event well-formedness --------------------------------------
    for e in g.events:
        if e.target not in g.vertices:
            issues.append(Issue("WF", e.eid, "target vertex missing"))
            continue
        t = g.vertices[e.target]
        for s in e.sources:
            if s not in g.vertices:
                issues.append(Issue("WF", e.eid, f"source vertex {s} missing"))

        # leaf events ------------------------------------------------------
        if e.rule == "Assume":
            if e.sources:
                issues.append(Issue("WF", e.eid, "Assume must have no sources"))
            if len(t.gamma) != 1 or lookup(t.gamma, next(iter(dom(t.gamma)))) != t.phi:
                issues.append(Issue("WF", e.eid,
                                    "Assume leaf must be {a:φ} ⊢ φ"))
            continue
        if e.rule == "Axiom":
            if e.sources or t.gamma:
                issues.append(Issue("WF", e.eid, "Axiom must be · ⊢ φ with no sources"))
            continue

        if e.rule == "Step":
            # Generic variadic computational step (used for ingested real-corpus
            # proofs whose inferences are not propositional ND rules): the
            # contents are opaque, so the schema-matching conditions (a)-(c) do
            # not apply, but the structural layer still applies — a derived step
            # must have at least one premise, and the context-flow / discharge /
            # acyclicity / unique-justification conditions are enforced.
            if not e.sources:
                issues.append(Issue("E1", e.eid, "derived step has no premises"))
            src_ctxs = [g.vertices[s].gamma for s in e.sources if s in g.vertices]
            u = union_consistent(src_ctxs)
            if u is None:
                issues.append(Issue("E2", e.eid, "inconsistent source contexts"))
            elif restrict(u, e.discharged) != t.gamma:
                issues.append(Issue("E2", e.eid, "context-flow mismatch (Γ_t ≠ (⊎Γ_s)↾(dom∖D))"))
            continue

        sch = lib.get(e.rule)
        if sch is None:
            issues.append(Issue("WF", e.eid, f"unknown rule {e.rule!r}"))
            continue
        sigma = e.subst()

        # (a) premises / (E1)
        prem = [apply_subst(p, sigma) for p in sch.premises]
        src_contents = [g.vertices[s].phi for s in e.sources if s in g.vertices]
        if _multiset(src_contents) != _multiset(prem):
            issues.append(Issue("E1", e.eid,
                f"sources {[str(x) for x in src_contents]} ≠ Prem {[str(x) for x in prem]}"))

        # (b) conclusion / (E1b)
        conc = apply_subst(sch.conclusion, sigma)
        if t.phi != conc:
            issues.append(Issue("E1b", e.eid, f"target {t.phi} ≠ Conc {conc}"))

        # (d) activation condition / (E2)
        src_ctxs = [g.vertices[s].gamma for s in e.sources if s in g.vertices]
        u = union_consistent(src_ctxs)
        if u is None:
            issues.append(Issue("E2", e.eid, "inconsistent source contexts (same id, two formulas)"))
        else:
            expected = restrict(u, e.discharged)
            if expected != t.gamma:
                issues.append(Issue("E2", e.eid,
                    f"Γ_t {{{_show(t.gamma)}}} ≠ (⊎Γ_s)↾(dom∖D) {{{_show(expected)}}}"))

        # (e) discharge coherence / (E3): each discharged id must be open in a
        # source and carry one of the rule's dischargeable formulas; it must not
        # remain open in the target. The number of discharged ids may be zero
        # (vacuous discharge) or more (multiple discharge), exactly as in
        # standard natural deduction -- the rule fixes *which* formula may be
        # discharged (via σ on the antecedent), not how many occurrences.
        disch_allowed = {apply_subst(d, sigma) for d in sch.discharges}
        if u is not None:
            for a in e.discharged:
                f = lookup(u, a)
                if f is None:
                    issues.append(Issue("E3", e.eid,
                        f"discharged id {a} is not open in any source context"))
                    continue
                if a in dom(t.gamma):
                    issues.append(Issue("E3", e.eid,
                        f"discharged id {a} still open in the target context"))
                if f not in disch_allowed:
                    issues.append(Issue("E3", e.eid,
                        f"rule {e.rule} may not discharge {f} "
                        f"(allowed: {[str(x) for x in disch_allowed] or ['∅']})"))

    # -- 2. acyclicity of the event-dependency order (occurrence DAG) -------
    if _has_cycle(g):
        issues.append(Issue("ACY", "—", "event-dependency order contains a cycle"))

    return CheckResult(ok=not issues, issues=issues,
                       input_size=g.input_size(), edges=len(g.events))


def _show(gamma) -> str:
    return ",".join(sorted(f"{a}:{f}" for a, f in gamma))


def _has_cycle(g: TCIH) -> bool:
    """DFS cycle detection on the vertex digraph (source -> target)."""
    adj: Dict[str, List[str]] = {v: [] for v in g.vertices}
    for e in g.events:
        for s in e.sources:
            if s in adj and e.target in g.vertices:
                adj[s].append(e.target)
    WHITE, GREY, BLACK = 0, 1, 2
    color = {v: WHITE for v in g.vertices}

    def dfs(u: str) -> bool:
        color[u] = GREY
        for w in adj[u]:
            if color[w] == GREY:
                return True
            if color[w] == WHITE and dfs(w):
                return True
        color[u] = BLACK
        return False

    return any(color[v] == WHITE and dfs(v) for v in g.vertices)


__all__ = ["Issue", "CheckResult", "TAXONOMY", "structural_check"]
