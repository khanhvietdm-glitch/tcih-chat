"""Produce a STRUCTURE-ONLY view of the proof-graph corpus for public release:
remove all natural-language content (problem text, step text, answers) and keep
only the graph topology, node kinds, rule premises/conclusions, edge evidence
types, and per-proof statistics. This lets reviewers verify the *structural*
results (Tables 10–13) without redistributing the source solution text.

Usage:
    python strip_corpus.py --samples        # strip data/sample/*.jsonl in place
    python strip_corpus.py --full OUTDIR     # write a stripped copy of out/ to OUTDIR
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def strip_record(rec: dict) -> dict:
    """Keep graph structure + stats; drop all prose (problem / text / answer)."""
    out = {"id": rec.get("id")}
    vf = []
    for v in rec.get("V_F", []):
        nv = {"id": v["id"], "kind": v["kind"]}
        if "step" in v:
            nv["step"] = v["step"]
        vf.append(nv)
    out["V_F"] = vf
    out["V_R"] = [{"id": r["id"], "premises": r["premises"],
                   "conclusion": r["conclusion"], "evidence": r.get("evidence", [])}
                  for r in rec.get("V_R", [])]
    out["E"] = rec.get("E", [])
    out["stats"] = rec.get("stats", {})
    return out


def strip_file(src: Path, dst: Path) -> int:
    dst.parent.mkdir(parents=True, exist_ok=True)
    n = 0
    with src.open("r", encoding="utf-8") as fin, dst.open("w", encoding="utf-8") as fout:
        for line in fin:
            line = line.strip()
            if not line:
                continue
            fout.write(json.dumps(strip_record(json.loads(line)), ensure_ascii=False) + "\n")
            n += 1
    return n


def strip_samples() -> None:
    d = HERE / "data" / "sample"
    for f in sorted(d.glob("*.graph.jsonl")):
        tmp = f.with_suffix(".tmp")
        n = strip_file(f, tmp)
        tmp.replace(f)
        print(f"stripped {f.name}: {n} records")


def strip_full(outdir: Path) -> None:
    src_root = HERE / "out"
    total = 0
    for src in sorted(src_root.rglob("*.graph.jsonl")):
        rel = src.relative_to(src_root)
        dst = outdir / rel
        total += strip_file(src, dst)
    # include the (prose-free) aggregate summary
    summ = src_root / "_summary.json"
    if summ.exists():
        (outdir / "_summary.json").write_text(summ.read_text(encoding="utf-8"), encoding="utf-8")
    print(f"stripped full corpus -> {outdir}  ({total} records)")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--samples", action="store_true")
    ap.add_argument("--full", type=Path, default=None)
    a = ap.parse_args()
    if a.samples:
        strip_samples()
    if a.full:
        strip_full(a.full)
    if not a.samples and not a.full:
        ap.print_help()


if __name__ == "__main__":
    main()
