# TCIH-Chat — a verified mathematics proof-assistant chatbot

Reference implementation accompanying the manuscript

> *A Typed Event-Hypergraph Framework for a Trustworthy Mathematics
> Proof-Assistant Chatbot: Automated Construction and Structural Diagnosis of
> Human- and LLM-Generated Proofs.*

This is the **corrected** reference core (v2.0). It re-implements the formal
model from scratch following the editorial review: vertices are **labelled
judgments** `v = (id, Γ⊢φ, τ)` with `Γ : AssumptionID ⇀ Form`, and a proof is
an **ordered event-hypergraph** `e = (S, t, R[σ], D, prov)`. Discharge is by
assumption identifier and event order, never by a mutable vertex flag.

The package is **dependency-free** (Python ≥ 3.10, standard library only).

## Quick start

```bash
# run the machine-checked regression suite (one test per review correction)
PYTHONUTF8=1 python -m pytest -q

# regenerate every numerical artefact cited in the paper
PYTHONUTF8=1 python run_artifacts.py        # -> artifacts/results.json

# talk to the assistant
PYTHONUTF8=1 python -m tcih.chatbot
∴ prove (A->B)->((B->C)->(A->C))
∴ prove ~P | P->Q, ~Q
∴ valid ~~A -> A
```

(`PYTHONUTF8=1` only matters on Windows consoles, so the logical symbols print.)

## Module map

| File | Role | Paper section |
|------|------|---------------|
| `tcih/formula.py` | propositional formulas, substitution, parser | §3.1 |
| `tcih/model.py` | labelled-judgment vertices, event-hypergraph, builder | §3.2–3.3 |
| `tcih/rules.py` | natural-deduction rule schemas | §3.4 |
| `tcih/check.py` | `StructuralCheck` (linear-time well-formedness) | §4, Alg.1 |
| `tcih/oracle.py` | semantic edge validity (propositional truth tables) | §4.2 |
| `tcih/smt_oracle.py` | SMT/CAS oracle (Z3 + SymPy); ground + contextual entailment | §6.3, §8.10–8.11 |
| `tcih/lean_backend.py` | Lean 4 kernel backend: `decide` (ground) + mathlib `nlinarith` (nonlinear) | §6.3, §8.12 |
| `tcih/fold.py` | folding + rank-based quotient acyclicity | §5.2 |
| `tcih/granularity.py` | macro expand/contract with provenance | §5.3 |
| `tcih/prover.py` | G4ip decision procedure + ND proof constructor | §6 |
| `tcih/search.py` | Horn forward chaining + corrected A* | §5.4 |
| `tcih/diagnose.py` | error taxonomy, localization, injection harness | §7 |
| `tcih/chatbot.py` | the conversational assistant (application layer) | §6 |
| `tcih/nl_parser.py` | rule-classifying corpus parser (D4→D5 upgrade) | §8.9 |
| `tcih/gallery.py` | corrected case-study derivations | Appendix |
| `proof_graph_parser.py` | legacy corpus ingestion (prose → proof graph) | §8 dataset |
| `corpus_stats.py` | real-corpus distributions → `artifacts/corpus_stats.json` | §8.8 |
| `run_corpus_eval.py` | upgraded parser + corpus error detection → `corpus_eval.json` | §8.9 |
| `run_semantic_eval.py` | SMT/CAS oracle over corpus → `artifacts/semantic_eval.json` | §8.10 |
| `run_context_eval.py` | contextual SMT (entailment under assumptions) → `context_eval.json` | §8.11 |
| `run_lean_eval.py` | Lean 4 ↔ Z3 agreement on corpus arithmetic → `lean_eval.json` | §8.12 |
| `make_figures.py` | renders pipeline / scaling / coverage figures | Figs 1, 3, 4 |
| `make_corpus_figures.py` | renders real corpus proof graphs (new parser, English) | Figs 5–8 |

## How the code answers each review point

| Review issue | Where it is fixed / demonstrated |
|--------------|----------------------------------|
| 4.1 discharge ⊄ premises | `rules.py` discharges are separate from premises |
| 4.2 context loses identity | `model.Context` = labelled `AssumptionID ⇀ Form` |
| 4.3 mutable δ flag | no flag; open/dis derived from `Event.discharged` + order |
| 4.4 / 4.8 folding | `fold.content_only_fold` rejected; `context_preserving_fold` sound |
| 4.5 `⊢ A⇒A` unrepresentable | `gallery.a_imp_a` (passes the checker) |
| 4.6 closure = length | restricted to Horn (`search.forward_chain`) |
| 4.7 Prop 4.6.1 false | `fold.antichain_counterexample`, `fold.rank_certifies_acyclic` |
| 4.9 granularity overstated | `granularity.length_law` (macro elimination + provenance) |
| 4.11 input size / σ vs unification | `model.input_size`, checker *verifies* supplied σ |
| 4.12 A* min(h,b) wrong | `search.admissibility_counterexample`, certified lower bound |
| 4.13 De Morgan not equivalence | `prover.ipc_provable` rejects `¬(A∧B)→(¬A∨¬B)` |

## Data

The proof-graph corpus (D4) is published **structure-only** — graph topology,
node kinds, edge provenance, and per-proof statistics, with all natural-language
solution text removed (`strip_corpus.py`) to respect the source licence. A small
sample is in [`data/sample/`](data/sample/); the full corpus is a release asset
(`corpus_full_structure_only.tar.gz`). See [`data/README.md`](data/README.md).
The structure-only data reproduces the structural results (Tables 10–13);
the semantic-oracle results (Tables 14–16) need the original text, available
from the authors on request.

## Reproducibility

Tag the released commit, archive it (Zenodo) and cite the DOI. Record the Python
version and `pip freeze` output. `python run_artifacts.py` regenerates
`artifacts/results.json` deterministically.
