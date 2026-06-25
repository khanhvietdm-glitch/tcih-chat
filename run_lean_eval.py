"""Run the Lean 4 kernel backend on a sample of the corpus's ground arithmetic
and measure agreement with the Z3/SymPy oracle (a higher-assurance cross-check),
plus Lean's detection of injected corrupted equalities.

Lean is slow (each query spawns the compiler), so this uses a small sample.
Writes artifacts/lean_eval.json. Requires a Lean toolchain on PATH.
"""
from __future__ import annotations

import json
import time
from pathlib import Path

from tcih.smt_oracle import step_claims, _to_expr, _decide
from tcih.lean_backend import check_arith, lean_available

HERE = Path(__file__).resolve().parent
OUT = HERE / "out"
ART = HERE / "artifacts"
K_AGREE = 120
K_INJECT = 30


def records():
    for fp in sorted(OUT.rglob("*.graph.jsonl")):
        with fp.open("r", encoding="utf-8") as fh:
            for line in fh:
                line = line.strip()
                if line:
                    yield json.loads(line)


def ground_claims(limit):
    out = []
    for rec in records():
        for v in rec["V_F"]:
            if v["kind"] != "derived":
                continue
            for ls, rs, op in step_claims(v.get("text", "")):
                L, R = _to_expr(ls), _to_expr(rs)
                if L is None or R is None or L.free_symbols or R.free_symbols:
                    continue
                out.append((L, R, op))
                if len(out) >= limit:
                    return out
    return out


def main():
    if not lean_available():
        print("Lean toolchain not available — skipping.")
        return
    import sympy
    t0 = time.perf_counter()
    samples = ground_claims(K_AGREE)
    agree = 0
    both_decided = 0
    disagreements = []
    for L, R, op in samples:
        z = _decide(L, R, op)
        zlab = "valid" if z is True else "invalid" if z is False else "unknown"
        llab = check_arith(L, R, op)
        if zlab != "unknown" and llab != "unknown":
            both_decided += 1
            if zlab == llab:
                agree += 1
            else:
                disagreements.append(f"{L} {op} {R}: z3={zlab} lean={llab}")

    # injection: corrupt true ground equalities and confirm Lean flags them
    eqs = [(L, R) for (L, R, op) in samples if op == "=" and _decide(L, R, "=") is True]
    inj_n = inj_hit = 0
    for L, R in eqs[:K_INJECT]:
        inj_n += 1
        if check_arith(L, R + 1, "=") == "invalid":
            inj_hit += 1

    dt = time.perf_counter() - t0
    result = {
        "lean_version": "leanprover/lean4:v4.31.0 (no mathlib)",
        "sample_claims": len(samples),
        "both_decided": both_decided,
        "lean_z3_agreement": round(agree / max(both_decided, 1), 4),
        "disagreements": disagreements[:10],
        "lean_injection": {"n": inj_n, "recall": round(inj_hit / max(inj_n, 1), 4)},
        "seconds": round(dt, 1),
    }
    ART.mkdir(exist_ok=True)
    (ART / "lean_eval.json").write_text(json.dumps(result, ensure_ascii=False, indent=2),
                                        encoding="utf-8")
    print(f"sample claims        : {len(samples)}  ({dt:.1f}s)")
    print(f"both decided (z3&lean): {both_decided}")
    print(f"Lean–Z3 agreement    : {result['lean_z3_agreement']}")
    print(f"disagreements        : {result['disagreements'] or 'none'}")
    print(f"Lean injection recall: {result['lean_injection']['recall']} (n={inj_n})")
    print(f"\nwrote {ART/'lean_eval.json'}")


if __name__ == "__main__":
    main()
