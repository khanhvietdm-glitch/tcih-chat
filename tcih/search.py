"""Proof search: Horn forward chaining and corrected A* heuristic search.

Two algorithmic results from the paper:

  * `forward_chain` -- linear-time forward chaining for the definite-Horn
    (monotone, discharge-free) fragment, the setting in which the closure
    operator, shortest path and proof length genuinely coincide (review issue
    4.6). Imported Dowling–Gallier result, recast on TCIH hyperedges.

  * `astar` + `admissibility_counterexample` -- the corrected admissibility
    story (review issue 4.12). The previously proposed correction
    h(v) ← min(h(v), b(v)) with an *upper* bound b does NOT restore
    admissibility; `admissibility_counterexample` exhibits h*=5, h=10, b=8 with
    min(h,b)=8>5. The correct device is a *certified lower bound* h̲ with
    0 ≤ h̲ ≤ h*; and for graph search, admissibility-without-consistency requires
    node reopening.
"""
from __future__ import annotations

import heapq
from typing import Callable, Dict, List, Optional, Set, Tuple


# --------------------------------------------------------------------------- #
# Horn forward chaining (Dowling–Gallier, on TCIH hyperedges)
# --------------------------------------------------------------------------- #
HornRule = Tuple[Tuple[str, ...], str]      # (premise atoms, conclusion atom)


def forward_chain(facts: Set[str], rules: List[HornRule]) -> Dict:
    """Compute the Horn closure in time linear in the total rule size; return the
    closure plus the proof DAG (which rule fired for each derived atom)."""
    closure: Set[str] = set(facts)
    derived_by: Dict[str, int] = {}                 # atom -> rule index that derived it
    counts = [len(prem) for prem, _ in rules]       # unmet premises per rule
    watch: Dict[str, List[int]] = {}
    for i, (prem, _) in enumerate(rules):
        for p in set(prem):
            watch.setdefault(p, []).append(i)
    queue = list(facts)
    fired = 0
    for i, (prem, c) in enumerate(rules):
        if not prem and c not in closure:           # rules with no premises
            closure.add(c); derived_by[c] = i; queue.append(c)
    while queue:
        a = queue.pop()
        for i in watch.get(a, []):
            counts[i] -= 1
            if counts[i] == 0:
                _, c = rules[i]
                fired += 1
                if c not in closure:
                    closure.add(c); derived_by[c] = i; queue.append(c)
    return {"closure": closure, "derived_by": derived_by, "rules_fired": fired}


# --------------------------------------------------------------------------- #
# A* with optional reopening; correct admissibility handling
# --------------------------------------------------------------------------- #
Graph = Dict[str, List[Tuple[str, float]]]      # node -> [(succ, weight)]


def astar(graph: Graph, start: str, goal: str,
          h: Callable[[str], float], reopen: bool = True) -> Dict:
    """A* graph search. With `reopen=True` a closed node is re-expanded when a
    cheaper path is found, which preserves optimality for admissible (not
    necessarily consistent) heuristics."""
    g_cost: Dict[str, float] = {start: 0.0}
    came: Dict[str, str] = {}
    open_heap: List[Tuple[float, str]] = [(h(start), start)]
    closed: Set[str] = set()
    expansions = 0
    while open_heap:
        f, u = heapq.heappop(open_heap)
        if u == goal:
            path = [u]
            while u in came:
                u = came[u]; path.append(u)
            return {"path": path[::-1], "cost": g_cost[goal], "expansions": expansions}
        if u in closed and not reopen:
            continue
        closed.add(u)
        expansions += 1
        for v, w in graph.get(u, []):
            ng = g_cost[u] + w
            if v not in g_cost or ng < g_cost[v]:
                g_cost[v] = ng
                came[v] = u
                if reopen:
                    closed.discard(v)
                heapq.heappush(open_heap, (ng + h(v), v))
    return {"path": None, "cost": float("inf"), "expansions": expansions}


def admissibility_counterexample() -> Dict:
    """The reviewer's witness that min(h, upper_bound) need not be admissible."""
    h_star, h, b = 5, 10, 8
    return {"h_star": h_star, "h": h, "upper_bound_b": b,
            "min_h_b": min(h, b),
            "still_inadmissible": min(h, b) > h_star,
            "fix": "use a certified lower bound h̲ with 0 ≤ h̲ ≤ h*"}


def demo_graph() -> Tuple[Graph, str, str, Dict[str, int]]:
    """Small graph with true cost-to-go h*. Optimal S→A→C→G costs 4; the direct
    edge S→G costs 5. A heuristic that *overestimates* the good path (h(A)>h*(A))
    diverts A* to the worse goal edge."""
    graph: Graph = {
        "S": [("A", 1), ("G", 5)],
        "A": [("C", 1)],
        "C": [("G", 2)],
        "G": [],
    }
    h_star = {"S": 4, "A": 3, "C": 2, "G": 0}      # exact cost-to-go (consistent)
    return graph, "S", "G", h_star


def astar_admissibility_demo() -> Dict:
    """Admissible (certified lower-bound) heuristic returns the optimal proof;
    an inadmissible (overestimating) one returns a sub-optimal one even with
    reopening -- the failure mode of the bogus min(h, upper_bound) rule."""
    graph, s, t, h_star = demo_graph()
    admissible = lambda n: h_star[n]                       # certified lower bound
    overestimate = {"S": 4, "A": 5, "C": 2, "G": 0}        # h(A)=5 > h*(A)=3
    opt = astar(graph, s, t, admissible, reopen=True)
    bad = astar(graph, s, t, lambda n: overestimate[n], reopen=True)
    return {
        "optimal_cost": opt["cost"], "optimal_path": opt["path"],
        "admissible_returns_optimal": opt["cost"] == 4,
        "inadmissible_cost": bad["cost"], "inadmissible_path": bad["path"],
        "inadmissible_suboptimal": bad["cost"] > opt["cost"],
    }


__all__ = ["forward_chain", "astar", "admissibility_counterexample",
           "demo_graph", "astar_admissibility_demo"]
