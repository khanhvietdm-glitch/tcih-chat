"""D4 → D5: run the rule-classifying parser on the real corpus, run the
corrected structural checker on the resulting TCIHs, and measure error detection
on real proof structures with injected ground-truth faults.

Outputs artifacts/corpus_eval.json and a printed summary. Everything here is
MEASURED on the real corpus (out/**/*.graph.jsonl); only the natural human/LLM
*semantic* error distribution remains out of scope (see the paper's limitations).
"""
from __future__ import annotations

import json
import time
from collections import Counter
from dataclasses import replace
from pathlib import Path

from tcih.check import structural_check
from tcih.nl_parser import reparse_edges, to_tcih, dependency_gaps, classify
from tcih.model import Event, Vertex
from tcih.formula import Atom

HERE = Path(__file__).resolve().parent
OUT = HERE / "out"
ART = HERE / "artifacts"
ART.mkdir(exist_ok=True)

MAX_RECORDS = 30000          # heavy eval sample (parser + checker)
INJECT_RECORDS = 4000        # error-injection sample


def records(limit):
    n = 0
    for fp in sorted(OUT.rglob("*.graph.jsonl")):
        with fp.open("r", encoding="utf-8") as fh:
            for line in fh:
                line = line.strip()
                if not line:
                    continue
                yield json.loads(line)
                n += 1
                if n >= limit:
                    return


def corpus_diagnose(g, record, edges):
    """Combined corpus diagnosis: the corrected structural checker (cycle,
    dangling, justification, empty-premise) plus the parser-level
    dependency-consistency check (missing semantic dependency)."""
    res = structural_check(g)
    classes = set()
    locus = None
    for iss in res.issues:
        if iss.code == "ACY":
            classes.add("cycle")
        elif iss.code == "WF" and "no justifying" in iss.message:
            classes.add("missing_justification"); locus = locus or iss.where
        elif iss.code == "WF" and "missing" in iss.message:
            classes.add("dangling_ref"); locus = locus or iss.where
        elif iss.code == "E1":
            classes.add("empty_premise"); locus = locus or iss.where
    gaps = dependency_gaps(record, edges)
    if gaps:
        classes.add("missing_dependency"); locus = locus or gaps[0]
    return classes, locus


def main():
    rule_dist = Counter()
    new_prov = Counter()
    legacy_prov = Counter()
    multi_source = 0
    derived_total = 0
    wellformed = 0
    acyclic = 0
    n = 0
    timing = []

    for rec in records(MAX_RECORDS):
        n += 1
        edges = reparse_edges(rec)
        # legacy provenance for contrast
        for r in rec.get("V_R", []):
            for ev in r.get("evidence", []):
                legacy_prov[ev.split(":", 1)[0]] += 1
        # new provenance + rule classes + multi-source
        for fid, info in edges.items():
            new_prov[info["evidence"]] += 1
            rule_dist[info["rule"]] += 1
            derived_total += 1
            if len(info["premises"]) >= 2:
                multi_source += 1
        g = to_tcih(rec, edges)
        N = g.input_size()
        t0 = time.perf_counter()
        res = structural_check(g)
        timing.append((N, time.perf_counter() - t0))
        wellformed += int(res.ok)
        acyclic += int(not any(i.code == "ACY" for i in res.issues))

    # ---- error injection on real structures ----------------------------
    classes = ["cycle", "dangling_ref", "missing_justification", "missing_dependency"]
    tp = Counter(); tot = Counter(); loc = Counter(); loc_tot = Counter()
    false_reject = 0
    clean_n = 0
    for rec in records(INJECT_RECORDS):
        edges = reparse_edges(rec)
        g = to_tcih(rec, edges)
        base_classes, _ = corpus_diagnose(g, rec, edges)
        if base_classes:
            false_reject += 1
        clean_n += 1
        nonleaf = [i for i, e in enumerate(g.events) if e.rule == "Step" and e.sources]
        if not nonleaf:
            continue
        ids = list(g.vertices)
        # cycle: find a derived step e2 depending on another derived step e1,
        # then add e2's target back as a source of e1 → a guaranteed 2-cycle.
        # (Applicable only when a derived→derived dependency exists.)
        target_event = {e.target: i for i, e in enumerate(g.events)}
        for i2, e2 in enumerate(g.events):
            if e2.rule != "Step":
                continue
            hit = next((s for s in e2.sources
                        if target_event.get(s) is not None
                        and g.events[target_event[s]].rule == "Step"
                        and target_event[s] != i2), None)
            if hit is not None:
                i1 = target_event[hit]
                gi = TCIH_copy(g)
                e1 = gi.events[i1]
                gi.events[i1] = replace(e1, sources=e1.sources + (e2.target,))
                c, _ = corpus_diagnose(gi, rec, edges)
                tot["cycle"] += 1; tp["cycle"] += int("cycle" in c)
                break

        # dangling ref
        gd = TCIH_copy(g)
        ev = gd.events[nonleaf[0]]
        gd.events[nonleaf[0]] = replace(ev, sources=("F_ghost",) + ev.sources[1:])
        c, l = corpus_diagnose(gd, rec, edges)
        tot["dangling_ref"] += 1; tp["dangling_ref"] += int("dangling_ref" in c)
        loc_tot["dangling_ref"] += 1; loc["dangling_ref"] += int(l == ev.eid)

        # missing justification: drop an event
        gj = TCIH_copy(g)
        drop = gj.events[nonleaf[0]]
        gj.events = [e for k, e in enumerate(gj.events) if k != nonleaf[0]]
        c, l = corpus_diagnose(gj, rec, edges)
        tot["missing_justification"] += 1
        tp["missing_justification"] += int("missing_justification" in c)
        loc_tot["missing_justification"] += 1
        loc["missing_justification"] += int(l == drop.target)

        # missing dependency: remove a value-match premise from a node whose
        # text justifies it (applicable only when such an edge exists)
        applicable = [(fid, info) for fid, info in edges.items()
                      if info["evidence"] == "value" and len(info["premises"]) >= 1]
        if applicable:
            fid, info = applicable[0]
            edges2 = {k: dict(v) for k, v in edges.items()}
            edges2[fid]["premises"] = info["premises"][1:] or ["F0"]
            g2 = to_tcih(rec, edges2)
            c, l = corpus_diagnose(g2, rec, edges2)
            tot["missing_dependency"] += 1
            tp["missing_dependency"] += int("missing_dependency" in c)
            loc_tot["missing_dependency"] += 1
            loc["missing_dependency"] += int(l == fid)

    def pct(c): return round(100 * c, 2)
    new_total = sum(new_prov.values()) or 1
    legacy_total = sum(legacy_prov.values()) or 1
    result = {
        "records_evaluated": n,
        "rule_class_distribution_pct": {k: pct(v / sum(rule_dist.values()))
                                        for k, v in rule_dist.most_common()},
        "legacy_edge_provenance_pct": {k: pct(v / legacy_total)
                                       for k, v in legacy_prov.most_common()},
        "new_edge_provenance_pct": {k: pct(v / new_total)
                                    for k, v in new_prov.most_common()},
        "multi_source_pct_new": pct(multi_source / max(derived_total, 1)),
        "structural_wellformed_pct": pct(wellformed / max(n, 1)),
        "acyclic_pct": pct(acyclic / max(n, 1)),
        "checker_us_per_N": round(1e6 * sum(d for _, d in timing) / max(sum(N for N, _ in timing), 1), 4),
        "error_detection": {
            "clean_proofs": clean_n,
            "false_rejection_rate": round(false_reject / max(clean_n, 1), 4),
            "per_class": {k: {"n": tot[k], "recall": round(tp[k] / tot[k], 3) if tot[k] else None,
                              "localization": round(loc[k] / loc_tot[k], 3) if loc_tot[k] else None}
                          for k in classes},
        },
    }
    (ART / "corpus_eval.json").write_text(json.dumps(result, ensure_ascii=False, indent=2),
                                          encoding="utf-8")
    print(f"records evaluated         : {n:,}")
    print(f"rule classes (%)          : {result['rule_class_distribution_pct']}")
    print(f"legacy edge provenance (%): {result['legacy_edge_provenance_pct']}")
    print(f"NEW edge provenance (%)   : {result['new_edge_provenance_pct']}")
    print(f"multi-source (new) %      : {result['multi_source_pct_new']}")
    print(f"structural well-formed %  : {result['structural_wellformed_pct']}  acyclic % {result['acyclic_pct']}")
    print(f"checker us/N              : {result['checker_us_per_N']}")
    ed = result["error_detection"]
    print(f"error detection (false-reject={ed['false_rejection_rate']}):")
    for k, v in ed["per_class"].items():
        print(f"   {k:22s} recall={v['recall']} localization={v['localization']} (n={v['n']})")
    print(f"\nwrote {ART/'corpus_eval.json'}")


def TCIH_copy(g):
    from tcih.model import TCIH
    return TCIH(dict(g.vertices), list(g.events))


if __name__ == "__main__":
    main()
