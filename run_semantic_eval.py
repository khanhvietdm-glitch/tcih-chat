"""Run the SMT/CAS semantic oracle over the real corpus: classify each step's
arithmetic claim as valid / invalid (E4) / symbolic / no-claim, report coverage
and any genuine arithmetic errors found, and measure E4-detection recall by
corrupting real ground equalities.

Writes artifacts/semantic_eval.json.
"""
from __future__ import annotations

import json
import time
from collections import Counter
from pathlib import Path

import sympy

from tcih.smt_oracle import step_claims, verify_step, _to_expr, _decide

HERE = Path(__file__).resolve().parent
OUT = HERE / "out"
ART = HERE / "artifacts"
MAX_RECORDS = 5000


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


def ground_equalities(text):
    """Return (L,R) sympy pairs for ground equalities in `text` that hold."""
    out = []
    for ls, rs, op in step_claims(text):
        if op != "=":
            continue
        L, R = _to_expr(ls), _to_expr(rs)
        if L is None or R is None or L.free_symbols or R.free_symbols:
            continue
        if _decide(L, R, "=") is True:
            out.append((L, R))
    return out


def main():
    status = Counter()
    steps = 0
    real_errors = []
    t0 = time.perf_counter()
    inj_n = inj_hit = 0

    for rec in records(MAX_RECORDS):
        for v in rec["V_F"]:
            if v["kind"] != "derived":
                continue
            text = v.get("text", "")
            steps += 1
            st = verify_step(text)
            status[st] += 1
            if st == "invalid" and len(real_errors) < 25:
                real_errors.append(text[:160])
            # E4 injection: corrupt one true ground equality (RHS + 1)
            for L, R in ground_equalities(text)[:1]:
                inj_n += 1
                if _decide(L, R + 1, "=") is False:
                    inj_hit += 1

    dt = time.perf_counter() - t0
    ground = status["valid"] + status["invalid"] + status["rounding"]
    result = {
        "records": MAX_RECORDS,
        "steps_checked": steps,
        "status_pct": {k: round(100 * status[k] / max(steps, 1), 2)
                       for k in ("valid", "rounding", "invalid", "symbolic", "no_claim")},
        "ground_checkable_pct": round(100 * ground / max(steps, 1), 2),
        "ground_validity_rate": round((status["valid"] + status["rounding"]) / max(ground, 1), 4),
        "genuine_arithmetic_errors_found": status["invalid"],
        "rounding_equalities": status["rounding"],
        "example_flagged_steps": real_errors[:10],
        "e4_injection": {"n": inj_n, "recall": round(inj_hit / max(inj_n, 1), 4)},
        "seconds": round(dt, 1),
        "backend": "Z3 (rationals) + SymPy (radicals) fallback; Lean = interface stub",
    }
    ART.mkdir(exist_ok=True)
    (ART / "semantic_eval.json").write_text(json.dumps(result, ensure_ascii=False, indent=2),
                                            encoding="utf-8")
    print(f"steps checked        : {steps:,}  ({dt:.1f}s)")
    print(f"status %             : {result['status_pct']}")
    print(f"ground-checkable %   : {result['ground_checkable_pct']}")
    print(f"ground validity rate : {result['ground_validity_rate']}")
    print(f"genuine errors found : {status['invalid']}   rounding(=for≈): {status['rounding']}")
    print(f"E4 injection recall  : {result['e4_injection']['recall']} (n={inj_n})")
    if real_errors:
        print("examples of flagged steps:")
        for e in real_errors[:5]:
            print("   •", e)
    print(f"\nwrote {ART/'semantic_eval.json'}")


if __name__ == "__main__":
    main()
