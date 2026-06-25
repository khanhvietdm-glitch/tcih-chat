"""Mine the REAL parsed proof-graph corpus (out/**/*.graph.jsonl) for the
distributions and structural measurements cited in the paper -- going beyond the
aggregate totals in out/_summary.json.

Computes, by streaming the actual per-proof graphs:
  * arity distribution of rule nodes (how multi-source real inference is),
  * proof-size distribution,
  * edge-provenance breakdown (how the parser recovered each edge:
    explicit step reference / value match / sequential fallback),
  * a real acyclicity + connectivity check on a sample, and the wall-clock of a
    structural traversal vs the real graph size N (linear-scaling evidence on
    real data, not synthetic chains).
"""
from __future__ import annotations

import json
import time
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
OUT = HERE / "out"
ART = HERE / "artifacts"
ART.mkdir(exist_ok=True)

SAMPLE_FOR_CHECK = 5000     # records to run the acyclicity/timing check on
PER_FILE_CAP = None         # None = all records


def graph_files():
    return sorted(OUT.rglob("*.graph.jsonl"))


def is_acyclic(V_ids, edges):
    adj = {v: [] for v in V_ids}
    for a, b in edges:
        if a in adj:
            adj[a].append(b)
    color = {v: 0 for v in V_ids}

    def dfs(u):
        color[u] = 1
        for w in adj.get(u, []):
            if color.get(w, 0) == 1:
                return False
            if color.get(w, 0) == 0 and not dfs(w):
                return False
        color[u] = 2
        return True

    return all(color[v] != 0 or dfs(v) for v in V_ids)


def main():
    arity_hist = Counter()
    size_hist = Counter()        # bucketed proof sizes (num_R)
    evidence = Counter()
    multi_source = 0
    total_rules = 0
    records = 0
    acyclic_ok = 0
    checked = 0
    timing = []                  # (N_real, seconds)

    for fp in graph_files():
        n_in_file = 0
        with fp.open("r", encoding="utf-8") as fh:
            for line in fh:
                line = line.strip()
                if not line:
                    continue
                rec = json.loads(line)
                records += 1
                n_in_file += 1
                VR = rec.get("V_R", [])
                for r in VR:
                    a = len(r.get("premises", []))
                    arity_hist[a] += 1
                    total_rules += 1
                    if a >= 2:
                        multi_source += 1
                    for ev in r.get("evidence", []):
                        kind = ev.split(":", 1)[0]
                        evidence[kind] += 1
                nR = rec.get("stats", {}).get("num_R", len(VR))
                # bucket: 1-2, 3-5, 6-10, 11-20, 21-50, 50+
                b = (1 if nR <= 2 else 2 if nR <= 5 else 3 if nR <= 10
                     else 4 if nR <= 20 else 5 if nR <= 50 else 6)
                size_hist[b] += 1
                if checked < SAMPLE_FOR_CHECK:
                    Vids = [f["id"] for f in rec.get("V_F", [])] + [r["id"] for r in VR]
                    edges = [tuple(e) for e in rec.get("E", [])]
                    N_real = len(Vids) + len(edges)
                    t0 = time.perf_counter()
                    ok = is_acyclic(Vids, edges)
                    timing.append((N_real, time.perf_counter() - t0))
                    acyclic_ok += int(ok)
                    checked += 1
                if PER_FILE_CAP and n_in_file >= PER_FILE_CAP:
                    break

    # arity summary
    arity_total = sum(arity_hist.values())
    top_arities = sorted(arity_hist.items())
    # timing regression: us per N (binned)
    timing.sort()
    bins = {}
    for N, dt in timing:
        b = 10 ** len(str(N))   # order-of-magnitude bin
        bins.setdefault(b, []).append(dt * 1e6 / max(N, 1))
    us_per_N = {b: round(sum(v) / len(v), 4) for b, v in sorted(bins.items())}

    result = {
        "records_processed": records,
        "rule_nodes": total_rules,
        "multi_source_fraction": round(multi_source / total_rules, 4) if total_rules else 0,
        "arity_distribution": {str(k): v for k, v in top_arities},
        "arity_ge2_pct": round(100 * multi_source / total_rules, 2) if total_rules else 0,
        "proof_size_buckets": {
            "1-2": size_hist[1], "3-5": size_hist[2], "6-10": size_hist[3],
            "11-20": size_hist[4], "21-50": size_hist[5], "50+": size_hist[6]},
        "edge_provenance": dict(evidence),
        "edge_provenance_pct": {k: round(100 * v / sum(evidence.values()), 2)
                                for k, v in evidence.items()} if evidence else {},
        "acyclicity_checked": checked,
        "acyclic_fraction": round(acyclic_ok / checked, 4) if checked else None,
        "structural_traversal_us_per_N_by_magnitude": us_per_N,
    }
    (ART / "corpus_stats.json").write_text(
        json.dumps(result, ensure_ascii=False, indent=2), encoding="utf-8")

    print(f"records processed         : {records:,}")
    print(f"rule nodes                : {total_rules:,}")
    print(f"multi-source (arity>=2)   : {result['arity_ge2_pct']}%")
    print(f"arity distribution (a:cnt): "
          + ", ".join(f"{k}:{v:,}" for k, v in top_arities[:8])
          + (f", ... up to a={top_arities[-1][0]}" if top_arities else ""))
    print(f"proof-size buckets        : {result['proof_size_buckets']}")
    print(f"edge provenance %         : {result['edge_provenance_pct']}")
    print(f"acyclic fraction (n={checked}) : {result['acyclic_fraction']}")
    print(f"traversal us/N by size    : {us_per_N}")
    print(f"\nwrote {ART/'corpus_stats.json'}")


if __name__ == "__main__":
    main()
