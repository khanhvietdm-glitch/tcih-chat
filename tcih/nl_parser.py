"""A rule-classifying, dependency-faithful parser for the real proof corpus
(D4 → D5), upgrading the legacy two-level parser.

Two concrete improvements over `proof_graph_parser.py`, both measurable:

  1. **Rule classification.** Each step is classified into a computational
     inference taxonomy (Define, Compute, ApplyFact, Solve, Compare, Convert,
     Conclude, Generic) from textual/LaTeX cues, replacing the wildcard STEP.

  2. **Faithful edges.** A step depends on earlier steps whose *produced result*
     it actually *uses* (numeric or symbolic), and otherwise on the **problem
     hypothesis** F0 — never on the merely-previous step. This removes the
     legacy "sequential fallback" edges (60% of the corpus), which spuriously
     chained independent parallel computations, and surfaces genuine
     multi-source aggregation steps.

The module rebuilds the enriched record from the preserved step text and emits a
TCIH (problem = Axiom leaf; each step = a generic `Step` event) on which the
corrected `structural_check` runs directly.
"""
from __future__ import annotations

import re
from typing import Dict, List, Sequence, Set, Tuple

from .formula import Atom
from .model import EMPTY_CTX, Event, TCIH, Vertex

# ---------------------------------------------------------------------------
# Extraction
# ---------------------------------------------------------------------------
_MATH = re.compile(r"\\\((.+?)\\\)|\\\[(.+?)\\\]|\$\$(.+?)\$\$|\$([^$]+?)\$", re.DOTALL)
_NUM = re.compile(r"-?\d+(?:\.\d+)?")
_BOXED = re.compile(r"\\boxed\{([^{}]+)\}")
_STEPREF = re.compile(r"\b(?:from|in|by|using)\s+step\s+(\d+)", re.IGNORECASE)
_TRIVIAL = {"0", "1", "-1", "2", "x", "y", "z", "n", "a", "b", "c", "k", "i", "t"}


def _norm(tok: str) -> str:
    tok = tok.strip().rstrip(".,;")
    for j in ("\\$", "$", "\\,", "\\;", "\\!", " "):
        tok = tok.replace(j, "")
    return tok


def _math_bodies(text: str) -> List[str]:
    out = []
    for m in _MATH.finditer(text):
        b = next((g for g in m.groups() if g is not None), None)
        if b:
            out.append(b)
    return out


def produced(text: str) -> Set[str]:
    """Tokens that look like the *output* of a step: RHS of the last '=' in each
    math block, boxed values, and the numeric literals on those right sides."""
    res: Set[str] = set()
    for m in _BOXED.finditer(text):
        t = _norm(m.group(1))
        if t:
            res.add(t)
    for body in _math_bodies(text):
        parts = re.split(r"(?<![<>!:])=(?!=)", body)
        if len(parts) >= 2:
            rhs = parts[-1]
            t = _norm(rhs)
            if t:
                res.add(t)
            for n in _NUM.finditer(rhs):
                res.add(_norm(n.group(0)))
    return {r for r in res if r}


def used(text: str) -> Set[str]:
    toks: Set[str] = set()
    for n in _NUM.finditer(text):
        toks.add(_norm(n.group(0)))
    for body in _math_bodies(text):
        for atom in re.split(r"[=+\-*/(),\\\s]+", body):
            atom = _norm(atom)
            if len(atom) >= 2:
                toks.add(atom)
    return {t for t in toks if t}


# ---------------------------------------------------------------------------
# Rule classification
# ---------------------------------------------------------------------------
RULE_CLASSES = ["Define", "Convert", "ApplyFact", "Solve", "Compare",
                "Compute", "Conclude", "Generic"]

_CUES = [
    ("Define", re.compile(r"\b(let|denote|suppose|assume|define|set\b|break down|"
                          r"we need to determine|represents)\b", re.I)),
    ("Convert", re.compile(r"\bconvert|in terms of|rewrite as\b", re.I)),
    ("ApplyFact", re.compile(r"\b(by the|using the|we know|since|because|by\s+\w+'s|"
                             r"according to|formula|theorem|property|rule)\b", re.I)),
    ("Solve", re.compile(r"\b(solv|simplif|expand|factor|isolate|substitut|plug)\w*", re.I)),
    ("Compare", re.compile(r"(greater than|less than|at least|at most|>|<|\\geq|\\leq|≥|≤)", re.I)),
    ("Conclude", re.compile(r"\b(therefore|hence|thus|so the|in conclusion|"
                            r"the answer is|we get|this gives|final)\b", re.I)),
    ("Compute", re.compile(r"(calculat|comput|total|sum|product|cost of|number of|=)", re.I)),
]


def classify(text: str) -> str:
    for name, rx in _CUES:
        if rx.search(text):
            return name
    return "Generic"


# ---------------------------------------------------------------------------
# Faithful edge re-inference
# ---------------------------------------------------------------------------
def reparse_edges(record: Dict) -> Dict:
    """Recompute premises for each derived/goal node from preserved text.
    Returns {Fid: {'premises':[...], 'evidence':'explicit|value|hypothesis|answer',
                   'rule': <class>}}."""
    V_F = record["V_F"]
    problem = record.get("problem", "")
    answer = str(record.get("answer", ""))
    derived = [v for v in V_F if v["kind"] == "derived"]
    goal = next((v for v in V_F if v["kind"] == "goal"), None)

    prob_tokens = {_norm(n.group(0)) for n in _NUM.finditer(problem)}
    prod: Dict[str, Set[str]] = {"F0": prob_tokens}
    order: List[str] = ["F0"]
    text_of: Dict[str, str] = {"F0": problem}
    for v in derived:
        prod[v["id"]] = produced(v.get("text", ""))
        text_of[v["id"]] = v.get("text", "")
        order.append(v["id"])

    out: Dict[str, Dict] = {}
    for idx, v in enumerate(derived):
        fid = v["id"]
        text = text_of[fid]
        my_used = used(text)
        prem: List[str] = []
        ev = None
        # (1) explicit "step k"
        for m in _STEPREF.finditer(text):
            k = int(m.group(1))
            ref = f"F{k}"
            if ref in prod and ref != fid and ref in order[:order.index(fid)]:
                if ref not in prem:
                    prem.append(ref); ev = "explicit"
        # (2) result-value / expression match against EARLIER steps
        for prev in order[:order.index(fid)]:
            if prev == "F0":
                continue
            informative = {t for t in prod[prev]
                           if t and t not in _TRIVIAL and t not in prob_tokens}
            if informative & my_used:
                if prev not in prem:
                    prem.append(prev); ev = ev or "value"
        # (3) otherwise depend on the problem hypothesis (NOT the previous step)
        if not prem:
            prem.append("F0"); ev = "hypothesis"
        out[fid] = {"premises": prem, "evidence": ev, "rule": classify(text)}

    if goal is not None:
        gid = goal["id"]
        # goal depends on steps producing the answer value, else the last step
        ans_tok = _norm(answer)
        prem = [v["id"] for v in derived if ans_tok and ans_tok in prod.get(v["id"], set())]
        if not prem and derived:
            prem = [derived[-1]["id"]]
        out[gid] = {"premises": prem or ["F0"], "evidence": "answer", "rule": "Conclude"}
    return out


# ---------------------------------------------------------------------------
# TCIH construction + dependency-consistency (text vs graph)
# ---------------------------------------------------------------------------
def to_tcih(record: Dict, edges: Dict) -> TCIH:
    g = TCIH()
    # F0 = axiom (problem); every node an opaque atom, empty context
    for v in record["V_F"]:
        fid = v["id"]
        g.vertices[fid] = Vertex(fid, EMPTY_CTX, Atom(fid))
    g.events.append(Event("e_F0", (), "F0", "Axiom"))
    ei = 0
    for v in record["V_F"]:
        fid = v["id"]
        if fid == "F0":
            continue
        ei += 1
        prem = tuple(edges.get(fid, {}).get("premises", []))
        g.events.append(Event(f"e{ei}", prem, fid, "Step"))
    return g


def dependency_gaps(record: Dict, edges: Dict) -> List[str]:
    """E1-style check: a derived step that *uses* a value produced by an earlier
    step which is NOT among its premises (a missing dependency the text
    justifies). Returns the offending node ids."""
    V_F = record["V_F"]
    order = [v["id"] for v in V_F if v["kind"] in ("hypothesis", "derived")]
    prod = {"F0": {_norm(n.group(0)) for n in _NUM.finditer(record.get("problem", ""))}}
    text_of = {}
    for v in V_F:
        if v["kind"] == "derived":
            prod[v["id"]] = produced(v.get("text", ""))
            text_of[v["id"]] = v.get("text", "")
    gaps = []
    for v in V_F:
        if v["kind"] != "derived":
            continue
        fid = v["id"]
        my_used = used(text_of.get(fid, ""))
        prem = set(edges.get(fid, {}).get("premises", []))
        for prev in order[:order.index(fid)]:
            if prev in ("F0",) or prev in prem:
                continue
            informative = {t for t in prod.get(prev, set())
                           if t and t not in _TRIVIAL and t not in prod["F0"]}
            if informative & my_used:
                gaps.append(fid)
                break
    return gaps


__all__ = ["produced", "used", "classify", "RULE_CLASSES", "reparse_edges",
           "to_tcih", "dependency_gaps"]
