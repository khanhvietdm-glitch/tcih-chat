# Data — the TCIH proof-graph corpus (D4)

This directory documents the corpus used in Section 8 of the paper.

## What is here (committed to the repo)

| Path | Size | Contents |
|------|------|----------|
| `data/sample/*.graph.jsonl` | ~0.9 MB | A small, inspectable **sample** (structure only) — 150 proofs from each of five domains (algebra, number theory, geometry, calculus, probability/combinatorics) plus the full `logic_foundations` set. |
| `data/corpus_summary.json` | ~6 KB | Per-file **aggregate statistics** of the full corpus (record counts, total formula/rule nodes, max arity). Source of Table 10. |

## The full corpus (not in the git tree)

The full corpus is **211,922** parsed proof graphs. Because the per-domain files
are large and a multi-hundred-MB git history is impractical, the full
(structure-only) corpus is published as a **GitHub Release asset**
(`corpus_full_structure_only.tar.gz`) on this repository, regenerable with
`python strip_corpus.py --full <dir>`.

## Structure-only release (no prose)

To respect the licence of the source solutions, the **public corpus contains
graph structure and statistics only** — all natural-language content (problem
text, step text, answers) has been removed by `strip_corpus.py`. This is
sufficient to verify the **structural** results (Tables 10–13: node/arity
distributions, acyclicity, parser edge provenance, structural error detection).
Reproducing the **semantic** results (Tables 14–16: SMT/CAS and Lean checking)
requires the original solution text, which the authors can provide on request
subject to the source dataset's licence.

## Record format (stripped)

Each line of a `*.graph.jsonl` file is one proof, a JSON object:

```jsonc
{
  "id": "…",                                       // content hash
  "V_F": [ {"id":"F0","kind":"hypothesis"},
           {"id":"F1","kind":"derived","step":1}, …,
           {"id":"Fn+1","kind":"goal"} ],          // node kinds only (no text)
  "V_R": [ {"id":"R1","premises":["F0"],"conclusion":"F1","evidence":[…]}, … ],
  "E":   [ ["F0","R1"], ["R1","F1"], … ],
  "stats": {"num_F":…, "num_R":…, "num_E":…, "max_arity":…, "mean_arity":…}
}
```

`V_F` are formula nodes (kind + step index, prose removed), `V_R` are rule
(hyperedge) nodes, `E` is the bipartite edge list. The `evidence` field records
how the **legacy** parser inferred each edge (`explicit_ref` / `value_match` /
`sequential_default` / `final_answer`); see §8.8. The **upgraded** parser
(`tcih/nl_parser.py`, §8.9) re-derives faithful structure and underlies
Figures 5–8 (those figures were rendered before stripping and are included as
images).

## Reproduce the derived numbers

```bash
python corpus_stats.py        # Table 11 distributions  -> artifacts/corpus_stats.json
python run_corpus_eval.py     # Tables 12–13 (parser + structural detection)
python run_semantic_eval.py   # Table 14 (SMT/CAS oracle)   [needs z3-solver, sympy]
python run_context2_eval.py   # Table 15 (contextual SMT)
python run_lean_eval.py       # Table 16 (Lean–Z3 agreement) [needs a Lean toolchain]
```

## Provenance and licence

The proofs are parsed from step-structured mathematics solutions (`instructor_v2`).
**Redistribution of the underlying solution text is the responsibility of the
authors and must respect the source dataset's licence.** The parsing code and the
derived graph structures in this repository are released under the repository's
MIT licence; the *content* of the solutions retains the licence of its source.
