"""Automated propositional proving that emits verifiable TCIH derivations.

Two engines, cross-validating (paper, System Architecture):

  * `ipc_provable`  -- Dyckhoff's contraction-free sequent calculus G4ip/LJT, a
    *terminating, complete decision procedure* for intuitionistic propositional
    logic. It answers provability with a guarantee of termination.

  * `prove`         -- a natural-deduction backward search that returns an actual
    TCIH derivation (a proof object) which is then independently validated by
    `structural_check` (structural) and `oracle` (semantic). Classical goals are
    reached via reductio (RAA). Search builds an abstract proof term first and
    realizes only the successful branch, so the resulting TCIH carries no junk
    vertices and every vertex has a unique justification.

The separation mirrors the paper's dichotomy: G4ip *decides*, the ND constructor
*produces a checkable certificate*, and the verifier *trusts neither blindly*.
"""
from __future__ import annotations

from typing import Dict, FrozenSet, List, Optional, Tuple

from .formula import (And, Atom, BOT, Bot, Formula, Imp, Not, Or)
from .model import Builder, TCIH

# --------------------------------------------------------------------------- #
# Normalisation: treat ¬A as A ⇒ ⊥ for the decision procedure
# --------------------------------------------------------------------------- #
def _norm(phi: Formula) -> Formula:
    if isinstance(phi, Not):
        return Imp(_norm(phi.sub), BOT)
    if isinstance(phi, And):
        return And(_norm(phi.left), _norm(phi.right))
    if isinstance(phi, Or):
        return Or(_norm(phi.left), _norm(phi.right))
    if isinstance(phi, Imp):
        return Imp(_norm(phi.left), _norm(phi.right))
    return phi


# --------------------------------------------------------------------------- #
# G4ip / LJT: terminating decision procedure for IPC
# --------------------------------------------------------------------------- #
def ipc_provable(assumptions: List[Formula], goal: Formula) -> bool:
    """Decide Γ ⊢ goal in intuitionistic propositional logic (terminating)."""
    memo: Dict[Tuple[FrozenSet[Formula], Formula], bool] = {}
    g0 = frozenset(_norm(a) for a in assumptions)
    return _ljt(g0, _norm(goal), memo)


def _ljt(G: FrozenSet[Formula], goal: Formula, memo) -> bool:
    key = (G, goal)
    if key in memo:
        return memo[key]
    memo[key] = _ljt_compute(G, goal, memo)
    return memo[key]


def _ljt_compute(G: FrozenSet[Formula], goal: Formula, memo) -> bool:
    # axioms
    if goal in G or BOT in G:
        return True
    if isinstance(goal, Atom) and goal in G:
        return True

    # ---- invertible LEFT rules (apply one, deterministic recursion) -------
    for f in G:
        if isinstance(f, And):                              # L∧
            return _ljt((G - {f}) | {f.left, f.right}, goal, memo)
        if isinstance(f, Imp):
            a, b = f.left, f.right
            if isinstance(a, And):                          # L⇒∧
                return _ljt((G - {f}) | {Imp(a.left, Imp(a.right, b))}, goal, memo)
            if isinstance(a, Or):                            # L⇒∨
                return _ljt((G - {f}) | {Imp(a.left, b), Imp(a.right, b)}, goal, memo)
            if isinstance(a, Bot):                           # ⊥⇒B is useless
                return _ljt(G - {f}, goal, memo)
            if isinstance(a, Atom) and a in G:              # L⇒0 (atomic)
                return _ljt((G - {f}) | {b}, goal, memo)
    for f in G:
        if isinstance(f, Or):                               # L∨ (invertible, branch)
            return (_ljt((G - {f}) | {f.left}, goal, memo)
                    and _ljt((G - {f}) | {f.right}, goal, memo))

    # ---- invertible RIGHT rules ------------------------------------------
    if isinstance(goal, And):                               # R∧
        return _ljt(G, goal.left, memo) and _ljt(G, goal.right, memo)
    if isinstance(goal, Imp):                               # R⇒
        return _ljt(G | {goal.left}, goal.right, memo)

    # ---- non-invertible rules (backtracking) -----------------------------
    if isinstance(goal, Or):                                # R∨
        if _ljt(G, goal.left, memo) or _ljt(G, goal.right, memo):
            return True
    for f in G:                                             # L⇒⇒
        if isinstance(f, Imp) and isinstance(f.left, Imp):
            c, d = f.left.left, f.left.right
            b = f.right
            if (_ljt((G - {f}) | {Imp(d, b)}, Imp(c, d), memo)
                    and _ljt((G - {f}) | {b}, goal, memo)):
                return True
    return False


# --------------------------------------------------------------------------- #
# Natural-deduction proof constructor -> abstract proof term -> TCIH
# --------------------------------------------------------------------------- #
# Proof terms (abstract; realized into a TCIH by `_realize`):
#   ('hyp', aid)                         use an in-scope assumption
#   ('impI', aid, A, B, pt)              discharge aid:A in pt:B  ⊢ A⇒B
#   ('impE', A, B, ptf, pta)
#   ('andI', A, B, p1, p2)
#   ('andE1'|'andE2', A, B, p)
#   ('orI1', A, B, p) / ('orI2', A, B, p)
#   ('orE', A, B, C, pd, aid1, p1, aid2, p2)
#   ('notI', aid, A, pbot)
#   ('notE', A, pa, pna)
#   ('botE', goal, pbot)
#   ('raa', aid, A, pbot)

Scope = Tuple[Tuple[str, Formula], ...]


class _Searcher:
    def __init__(self, classical: bool, max_depth: int, budget: int = 60000):
        self.classical = classical
        self.max_depth = max_depth
        self.budget = budget
        self._aid = 0

    def fresh(self) -> str:
        self._aid += 1
        return f"h{self._aid}"

    def search(self, goal: Formula, scope: Scope, depth: int,
               path: FrozenSet[Tuple[FrozenSet[Formula], Formula]]):
        self.budget -= 1
        if self.budget <= 0 or depth < 0:
            return None
        skey = (frozenset(f for _, f in scope), goal)
        if skey in path:
            return None
        path = path | {skey}

        # (1) direct hypothesis
        for aid, f in scope:
            if f == goal:
                return ("hyp", aid)

        # (2) introduction on the goal
        if isinstance(goal, And):
            p1 = self.search(goal.left, scope, depth - 1, path)
            p2 = self.search(goal.right, scope, depth - 1, path)
            if p1 and p2:
                return ("andI", goal.left, goal.right, p1, p2)
        if isinstance(goal, Imp):
            aid = self.fresh()
            sub = self.search(goal.right, scope + ((aid, goal.left),), depth - 1, path)
            if sub:
                return ("impI", aid, goal.left, goal.right, sub)
        if isinstance(goal, Not):
            aid = self.fresh()
            sub = self.search(BOT, scope + ((aid, goal.sub),), depth - 1, path)
            if sub:
                return ("notI", aid, goal.sub, sub)

        # (3) elimination on assumptions
        r = self._eliminate(goal, scope, depth, path)
        if r:
            return r

        # (4) disjunction introduction (non-invertible, after elims)
        if isinstance(goal, Or):
            p = self.search(goal.left, scope, depth - 1, path)
            if p:
                return ("orI1", goal.left, goal.right, p)
            p = self.search(goal.right, scope, depth - 1, path)
            if p:
                return ("orI2", goal.left, goal.right, p)

        # (5) classical reductio
        if self.classical and not isinstance(goal, Bot):
            aid = self.fresh()
            sub = self.search(BOT, scope + ((aid, Not(goal)),), depth - 1, path)
            if sub:
                return ("raa", aid, goal, sub)
        return None

    def _eliminate(self, goal, scope, depth, path):
        for aid, f in scope:
            if isinstance(f, And):
                # project and retry with enriched scope
                ns = scope + ((self.fresh(), f.left), (self.fresh(), f.right))
                # mark projections by special hyp wrappers
                pj = self.search(goal, ns, depth - 1, path)
                if pj:
                    return self._wrap_and_proj(f, aid, ns, goal, pj, scope)
            if isinstance(f, Imp):
                pa = self.search(f.left, scope, depth - 1, path)
                if pa:
                    nid = self.fresh()
                    ns = scope + ((nid, f.right),)
                    cont = self.search(goal, ns, depth - 1, path)
                    if cont:
                        return self._let(nid, ("impE", f.left, f.right, ("hyp", aid), pa), ns, goal, cont, scope)
            if isinstance(f, Or):
                aid1, aid2 = self.fresh(), self.fresh()
                p1 = self.search(goal, scope + ((aid1, f.left),), depth - 1, path)
                p2 = self.search(goal, scope + ((aid2, f.right),), depth - 1, path)
                if p1 and p2:
                    return ("orE", f.left, f.right, goal, ("hyp", aid), aid1, p1, aid2, p2)
            if isinstance(f, Not):
                pa = self.search(f.sub, scope, depth - 1, path)
                if pa:
                    botpt = ("notE", f.sub, pa, ("hyp", aid))
                    if isinstance(goal, Bot):
                        return botpt
                    return ("botE", goal, botpt)
            if isinstance(f, Bot):
                return ("botE", goal, ("hyp", aid))
        return None

    # The "let" combinators below thread a freshly derived fact into a
    # continuation by substituting its proof term for the hyp reference.
    def _let(self, nid, fact_pt, ns, goal, cont, scope):
        return _subst_hyp(cont, nid, fact_pt)

    def _wrap_and_proj(self, f, aid, ns, goal, pj, scope):
        l_id, r_id = ns[-2][0], ns[-1][0]
        pj = _subst_hyp(pj, l_id, ("andE1", f.left, f.right, ("hyp", aid)))
        pj = _subst_hyp(pj, r_id, ("andE2", f.left, f.right, ("hyp", aid)))
        return pj


def _subst_hyp(pt, aid, replacement):
    """Replace ('hyp', aid) by `replacement` throughout the proof term."""
    if not isinstance(pt, tuple):
        return pt
    if pt[0] == "hyp":
        return replacement if pt[1] == aid else pt
    return tuple(_subst_hyp(x, aid, replacement) for x in pt)


# --------------------------------------------------------------------------- #
# Realization: abstract proof term -> TCIH (correct by construction)
# --------------------------------------------------------------------------- #
def _realize(term, hyps: Dict[str, Formula]) -> TCIH:
    b = Builder()
    env: Dict[str, str] = {}             # aid -> leaf vid (open assumptions)
    for aid, f in hyps.items():
        env[aid] = b.assume(f, aid=aid)

    def _used(vid: str, aid: str) -> bool:
        """Is assumption id `aid` open in the context of vertex vid?"""
        return any(a == aid for a, _ in b.g.vertices[vid].gamma)

    def go(pt) -> str:
        tag = pt[0]
        if tag == "hyp":
            return env[pt[1]]
        if tag == "impI":
            _, aid, A, B, sub = pt
            env[aid] = b.assume(A, aid=aid)
            vb = go(sub)
            d = [aid] if _used(vb, aid) else []   # vacuous discharge if unused
            return b.step("ImpI", [vb], Imp(A, B), discharge=d, sigma={"A": A, "B": B})
        if tag == "impE":
            _, A, B, pf, pa = pt
            return b.step("ImpE", [go(pf), go(pa)], B, sigma={"A": A, "B": B})
        if tag == "andI":
            _, A, B, p1, p2 = pt
            return b.step("AndI", [go(p1), go(p2)], And(A, B), sigma={"A": A, "B": B})
        if tag == "andE1":
            _, A, B, p = pt
            return b.step("AndE1", [go(p)], A, sigma={"A": A, "B": B})
        if tag == "andE2":
            _, A, B, p = pt
            return b.step("AndE2", [go(p)], B, sigma={"A": A, "B": B})
        if tag == "orI1":
            _, A, B, p = pt
            return b.step("OrI1", [go(p)], Or(A, B), sigma={"A": A, "B": B})
        if tag == "orI2":
            _, A, B, p = pt
            return b.step("OrI2", [go(p)], Or(A, B), sigma={"A": A, "B": B})
        if tag == "orE":
            _, A, B, C, pd, aid1, p1, aid2, p2 = pt
            vd = go(pd)
            env[aid1] = b.assume(A, aid=aid1)
            v1 = go(p1)
            env[aid2] = b.assume(B, aid=aid2)
            v2 = go(p2)
            d = ([aid1] if _used(v1, aid1) else []) + ([aid2] if _used(v2, aid2) else [])
            return b.step("OrE", [vd, v1, v2], C, discharge=d,
                          sigma={"A": A, "B": B, "C": C})
        if tag == "notI":
            _, aid, A, sub = pt
            env[aid] = b.assume(A, aid=aid)
            vbot = go(sub)
            d = [aid] if _used(vbot, aid) else []
            return b.step("NotI", [vbot], Not(A), discharge=d, sigma={"A": A})
        if tag == "notE":
            _, A, pa, pna = pt
            return b.step("NotE", [go(pa), go(pna)], BOT, sigma={"A": A})
        if tag == "botE":
            _, goal, pbot = pt
            return b.step("BotE", [go(pbot)], goal, sigma={"C": goal})
        if tag == "raa":
            _, aid, A, sub = pt
            env[aid] = b.assume(Not(A), aid=aid)
            vbot = go(sub)
            d = [aid] if _used(vbot, aid) else []
            return b.step("RAA", [vbot], A, discharge=d, sigma={"A": A})
        raise ValueError(f"unknown proof term {pt!r}")

    go(term)
    return b.build()


def prove(goal: Formula, assumptions: Optional[List[Formula]] = None,
          classical: bool = False, max_depth: int = 14) -> Optional[TCIH]:
    """Search for a natural-deduction proof of `goal` from `assumptions` and
    return it as a TCIH (or None if none is found within the depth bound)."""
    assumptions = assumptions or []
    hyps: Dict[str, Formula] = {}
    scope: Scope = ()
    for i, f in enumerate(assumptions):
        aid = f"g{i}"
        hyps[aid] = f
        scope = scope + ((aid, f),)
    for d in range(2, max_depth + 1):       # iterative deepening
        s = _Searcher(classical=classical, max_depth=d)
        term = s.search(goal, scope, d, frozenset())
        if term is not None:
            return _realize(term, hyps)
    return None


__all__ = ["ipc_provable", "prove"]
