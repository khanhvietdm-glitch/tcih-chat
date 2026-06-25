"""Contextual SMT evaluation: decide symbolic (in)equality steps UNDER the
assumptions established by their premise steps, extending semantic coverage
beyond the ground (variable-free) fragment of run_semantic_eval.py.

For each derived step we gather the variable-defining equalities of its
transitive premises (via the faithful nl_parser edges) and ask Z3 whether the
step's claim is entailed. Writes artifacts/context_eval.json.
"""
from __future__ import annotations

import json
import time
from collections import Counter
from pathlib import Path

from tcih.nl_parser import reparse_edges
from tcih.smt_oracle import step_claims, verify_step, verify_step_ctx, _to_expr

HERE = Path(__file__).resolve().parent
OUT = HERE / "out"
ART = HERE / "artifacts"
MAX_RECORDS = 2000


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


def defining_equalities(text):
    """Equalities 'symbol = expr' usable as assumptions (pin variables)."""
    out = []
    for ls, rs, op in step_claims(text):
        if op != "=":
            continue
        L, R = _to_expr(ls), _to_expr(rs)
        if L is None or R is None:
            continue
        if L.is_Symbol or R.is_Symbol:
            out.append((L, R, op))
    return out


def ancestors(fid, prem_map):
    seen, stack = set(), list(prem_map.get(fid, []))
    while stack:
        p = stack.pop()
        if p in seen:
            continue
        seen.add(p)
        stack.extend(prem_map.get(p, []))
    return seen


def main():
    base = Counter()       # verify_step (no context)
    ctx = Counter()        # verify_step_ctx (with assumptions)
    upgraded = 0           # symbolic -> decided by context
    ctx_invalid = 0
    steps = 0
    t0 = time.perf_counter()

    for rec in records(MAX_RECORDS):
        edges = reparse_edges(rec)
        prem_map = {fid: info["premises"] for fid, info in edges.items()}
        text_of = {v["id"]: v.get("text", "") for v in rec["V_F"]}
        text_of["F0"] = rec.get("problem", "")
        for v in rec["V_F"]:
            if v["kind"] != "derived":
                continue
            fid = v["id"]
            text = text_of[fid]
            steps += 1
            b = verify_step(text)
            base[b] += 1
            asm = []
            for anc in ancestors(fid, prem_map):
                asm.extend(defining_equalities(text_of.get(anc, "")))
            asm = asm[:15]
            c = verify_step_ctx(text, asm)
            ctx[c] += 1
            if b == "symbolic" and c in ("valid", "invalid"):
                upgraded += 1
            if c == "invalid" and b != "invalid":
                ctx_invalid += 1

    dt = time.perf_counter() - t0
    base_dec = base["valid"] + base["invalid"] + base["rounding"]
    ctx_dec = ctx["valid"] + ctx["invalid"] + ctx["rounding"]
    result = {
        "records": MAX_RECORDS, "steps": steps, "seconds": round(dt, 1),
        "baseline_decidable_pct": round(100 * base_dec / max(steps, 1), 2),
        "contextual_decidable_pct": round(100 * ctx_dec / max(steps, 1), 2),
        "coverage_gain_pct_points": round(100 * (ctx_dec - base_dec) / max(steps, 1), 2),
        "symbolic_upgraded_by_context": upgraded,
        "extra_invalids_with_context": ctx_invalid,
        "baseline_status_pct": {k: round(100 * base[k] / max(steps, 1), 2)
                                for k in ("valid", "invalid", "rounding", "symbolic", "no_claim")},
        "contextual_status_pct": {k: round(100 * ctx[k] / max(steps, 1), 2)
                                  for k in ("valid", "invalid", "rounding", "symbolic", "no_claim")},
    }
    ART.mkdir(exist_ok=True)
    (ART / "context_eval.json").write_text(json.dumps(result, ensure_ascii=False, indent=2),
                                           encoding="utf-8")
    print(f"steps {steps:,} in {dt:.1f}s")
    print(f"decidable: baseline {result['baseline_decidable_pct']}%  ->  "
          f"with context {result['contextual_decidable_pct']}%  "
          f"(+{result['coverage_gain_pct_points']} pts)")
    print(f"symbolic steps upgraded by context: {upgraded}")
    print(f"extra invalids surfaced with context: {ctx_invalid}")
    print(f"baseline : {result['baseline_status_pct']}")
    print(f"contextual: {result['contextual_status_pct']}")
    print(f"\nwrote {ART/'context_eval.json'}")


if __name__ == "__main__":
    main()
