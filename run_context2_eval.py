"""Enriched contextual SMT: add the PROBLEM statement's relations and NL
constraints (e.g. 'x is positive') to the premise-derived assumptions, and
measure the further coverage gain over premise-only context (run_context_eval).

Writes artifacts/context2_eval.json.
"""
from __future__ import annotations

import json
import time
from collections import Counter
from pathlib import Path

from tcih.nl_parser import reparse_edges
from tcih.smt_oracle import verify_step, verify_step_ctx, relations_of, nl_constraints

HERE = Path(__file__).resolve().parent
OUT = HERE / "out"
ART = HERE / "artifacts"
MAX_RECORDS = 1500


def records(limit):
    n = 0
    for fp in sorted(OUT.rglob("*.graph.jsonl")):
        with fp.open("r", encoding="utf-8") as fh:
            for line in fh:
                line = line.strip()
                if line:
                    yield json.loads(line)
                    n += 1
                    if n >= limit:
                        return


def ancestors(fid, prem_map):
    seen, stack = set(), list(prem_map.get(fid, []))
    while stack:
        p = stack.pop()
        if p not in seen:
            seen.add(p)
            stack.extend(prem_map.get(p, []))
    return seen


def main():
    base = Counter(); prem = Counter(); full = Counter()
    up_prem = up_full = 0
    steps = 0
    t0 = time.perf_counter()
    for rec in records(MAX_RECORDS):
        edges = reparse_edges(rec)
        prem_map = {fid: info["premises"] for fid, info in edges.items()}
        text_of = {v["id"]: v.get("text", "") for v in rec["V_F"]}
        problem = rec.get("problem", "")
        text_of["F0"] = problem
        prob_asm = relations_of(problem)[:10] + nl_constraints(problem)
        for v in rec["V_F"]:
            if v["kind"] != "derived":
                continue
            fid = v["id"]
            text = text_of[fid]
            steps += 1
            b = verify_step(text)
            base[b] += 1
            anc = ancestors(fid, prem_map)
            prem_rel = []
            for a in anc:
                if a != "F0":
                    prem_rel += relations_of(text_of.get(a, ""))
            prem_rel = prem_rel[:20]
            full_rel = (prem_rel + prob_asm)[:28]
            cp = verify_step_ctx(text, prem_rel)
            cf = verify_step_ctx(text, full_rel)
            prem[cp] += 1; full[cf] += 1
            if b == "symbolic" and cp in ("valid", "invalid"):
                up_prem += 1
            if cp == "symbolic" and cf in ("valid", "invalid"):
                up_full += 1

    dt = time.perf_counter() - t0

    def dec(c):
        return round(100 * (c["valid"] + c["invalid"] + c["rounding"]) / max(steps, 1), 2)
    result = {
        "records": MAX_RECORDS, "steps": steps, "seconds": round(dt, 1),
        "baseline_decidable_pct": dec(base),
        "premise_context_decidable_pct": dec(prem),
        "full_context_decidable_pct": dec(full),
        "problem_prose_extra_upgrades": up_full,
        "full_status_pct": {k: round(100 * full[k] / max(steps, 1), 2)
                            for k in ("valid", "invalid", "rounding", "symbolic", "no_claim")},
    }
    ART.mkdir(exist_ok=True)
    (ART / "context2_eval.json").write_text(json.dumps(result, ensure_ascii=False, indent=2),
                                            encoding="utf-8")
    print(f"steps {steps:,} in {dt:.1f}s")
    print(f"decidable: baseline {result['baseline_decidable_pct']}%  ->  "
          f"premise-context {result['premise_context_decidable_pct']}%  ->  "
          f"+problem-prose {result['full_context_decidable_pct']}%")
    print(f"extra upgrades from problem prose: {up_full}")
    print(f"full status: {result['full_status_pct']}")
    print(f"\nwrote {ART/'context2_eval.json'}")


if __name__ == "__main__":
    main()
