# 5. Algorithms and the Stratified Complexity Dichotomy

## 5.1. Encoded input size and the structural checker

The cost of structural checking must be stated against an explicit size model, not against $|V|+|E|$ alone.

> **Definition 5.1 (encoded input size).**
> $$N \;=\; \sum_{v\in V}\Bigl(|\varphi_v| + \!\!\sum_{(a,\psi)\in\Gamma_v}\!\!(1+|\psi|)\Bigr) \;+\; \sum_{e\in E}\Bigl(1+|S_e|+|D_e|+\!\!\sum_{(x,\psi)\in\sigma_e}\!\!|\psi|\Bigr).$$
> $N$ counts formula-string sizes, context sizes, source incidences, discharge identifiers and substitution sizes — the quantities a real implementation actually traverses.

Algorithm 1 (`StructuralCheck`) decides Definition 3.7 and acyclicity. A design point demanded by review is that it **verifies a supplied substitution** $\sigma_e$ attached to each event, rather than *searching* for a unifier: instantiating $\mathrm{Prem}(R)[\sigma_e]$ and comparing multisets is the cheap verification problem; finding $\sigma_e$ is the separate (and more expensive) unification/search problem handled by the prover.

> **Algorithm 1 — `StructuralCheck`($G,\mathcal R$).**
> For each event $e$: look up its schema; check the source-content multiset against $\mathrm{Prem}(R)[\sigma_e]$ (cond. 1) and the target against $\mathrm{Conc}(R)[\sigma_e]$ (cond. 2); check sorts (cond. 3); form $\biguplus_{s}\Gamma_s$ and compare $\Gamma_{t_e}$ to its restriction by $D_e$ (cond. 4); check that each $a\in D_e$ is open with a dischargeable formula and absent from $\Gamma_{t_e}$ (cond. 5). Then verify unique justification and run a DFS for acyclicity of $\prec$. Return the list of violated conditions.

> **Theorem 5.2 (correctness and complexity of `StructuralCheck`).** `StructuralCheck` returns *well-formed* iff $G$ satisfies Definition 3.7 and $\prec$ is acyclic. Under the standard assumption that formula equality and hashing are linear in formula size, it runs in $O(N)$ time (one pass over events, each touching its own incidences and substitution, plus one DFS), i.e. $O(N\log N)$ if an ordered map is used for contexts.

The empirical confirmation (Section 8, Table 6) shows the per-node cost is essentially constant across three orders of magnitude in $N$.

## 5.2. Folding with a rank certificate

Given a label-preserving candidate fold, the verifier merges classes, rebuilds events de-duplicating structurally identical ones, and tests the quotient for acyclicity by DFS; the rank function $\rho(v)=$ longest event-chain to $v$ is returned as a certificate (Proposition 4.5). The cost is $O(N)$.

## 5.3. Horn forward chaining (imported)

> **Theorem 5.3 (Dowling–Gallier, in TCIH form).** For a definite-Horn library and atomic assumptions $H$, $\mathrm{Cl}_\mathcal R(H)$ and a witnessing proof DAG are computable in time linear in the total rule size [26].

This is the one regime where the structural and semantic sides coincide and the whole derivation is polynomial (test `forward_chain`). It is *imported*, not new; we include it because it is exactly the monotone fragment of Proposition 3.12 and the base case of the dichotomy.

## 5.4. Heuristic search and the admissibility correction

Proof search over the state-transition graph is naturally A\* with a (possibly learned) heuristic. The precursor proposed to "repair" an inadmissible heuristic by $h(v)\leftarrow\min(h(v),b(v))$ with $b$ a feasible **upper** bound on the remaining cost. This does not restore admissibility.

> **Proposition 5.4 ($\min(h,b)$ is not a fix).** With $h^*(v)=5$, $h(v)=10$, $b(v)=8$, one has $\min(h,b)=8>5=h^*(v)$: the heuristic still overestimates, so A\* loses optimality.

> **Theorem 5.5 (correct admissibility handling).** A\* returns a shortest proof if the heuristic is a **certified lower bound** $\underline h$ with $0\le\underline h(v)\le h^*(v)$ (e.g. from a logical relaxation, or the constant $0$). A learned heuristic should be used only for tie-breaking/node-ordering over a guaranteed-admissible base. For graph search, admissibility without consistency requires node reopening.

*Demonstration (test `astar`).* On the demonstration graph (optimal cost $4$ via $S\!\to\!A\!\to\!C\!\to\!G$, direct edge $S\!\to\!G$ of cost $5$), the certified lower bound returns cost $4$, while an overestimating heuristic ($h(A)=5>3=h^*(A)$) returns the sub-optimal cost-$5$ path even with reopening. This is the failure mode $\min(h,b)$ would silently introduce.

## 5.5. The stratified dichotomy

> **Theorem 5.6 (stratified complexity dichotomy).** Fix a TCIH $G$ over a library $\mathcal R$, with encoded input size $N$.
> **(a) Structural well-formedness** (Definition 3.7) and acyclicity are decidable in $O(N)$ (Theorem 5.2).
> **(b) Definite-Horn entailment** (propositional or finite-ground) is linear [26].
> **(c) Verifying a supplied first-order substitution** is $O(N)$; *finding* a most general unifier is near-linear (Martelli–Montanari [48]). These are different problems and must not be conflated.
> **(d) Unification modulo an equational theory** is theory-dependent: AC-unification is decidable but NP-hard; unification modulo a general finitely-presented theory is undecidable.
> **(e) Propositional side-condition satisfiability** is NP-complete.
> **(f) First-order validity** is undecidable (Church–Turing); finite validity is undecidable by Trakhtenbrot's theorem.
> **(g) Dependent type checking** is theory-dependent, decidable for the Calculus of Constructions.

The dichotomy is the algorithmic backbone of TCIH-Chat: layer (a) is always run and always certain; the system then dispatches each semantic obligation to the cheapest sufficient stratum, escalating from (b) to (g) only as the content demands, and reporting honestly when an obligation is undecidable in the chosen logic.

---

# 6. TCIH-Chat: System Architecture

TCIH-Chat composes the verified core into a conversational assistant. Its defining guarantee is **no unverified proof is ever presented**: the trusted base is the small structural checker (Algorithm 1) plus the chosen oracle, *not* the (heuristic) prover and *not* any LLM placed in front of it.

## 6.1. Pipeline

A user turn is routed through five stages.

- **S1 — Intake.** A goal (and optional assumptions) in the ASCII/Unicode formula syntax, or a candidate proof to be checked, or a structured prose solution to be parsed into a TCIH.
- **S2 — Construction or ingestion.** For a goal, the automated prover (Section 6.2) constructs a derivation. For a candidate proof, the ingester builds the TCIH from the user's/LLM's steps.
- **S3 — Verification.** `StructuralCheck` decides well-formedness in linear time; the semantic oracle (Section 6.3) discharges each edge's validity at the cheapest sufficient stratum.
- **S4 — Diagnosis and localization.** If verification fails, the diagnoser (Section 6.4) classifies and localizes the error.
- **S5 — Explanation.** A verified proof is rendered at the requested granularity (Section 6.6).

![**Figure 1.** The TCIH-Chat pipeline. A goal, a candidate proof, or structured prose enters at S1 and is parsed into the shared TCIH event-hypergraph; S2 constructs a derivation (G4ip + the natural-deduction synthesizer) or ingests the user's/LLM's steps (`nl_parser`); S3 — the *trusted base* — runs the linear-time `StructuralCheck` and the four-tier semantic oracle (Z3 ground → Z3 contextual → Lean → mathlib); S4 classifies and localizes any failure to the smallest failing sub-derivation; S5 explains the verified proof at adjustable granularity. The dashed loop is the neuro-symbolic verify-and-repair cycle: localized, class-tagged feedback returned to the generator.](figures/fig_pipeline.png){width=100%}

## 6.2. The automated proving engine

The engine pairs two cross-validating components.

- A **terminating decision procedure**: Dyckhoff's contraction-free sequent calculus G4ip/LJT [49] decides intuitionistic propositional provability with a guarantee of termination. We use it to (i) answer "is this provable?" and (ii) decide whether to attempt an intuitionistic or a classical (reductio) construction.
- A **natural-deduction synthesizer**: an iterative-deepening backward search that returns an *abstract proof term*, of which only the successful branch is realized into a TCIH. The realization opens assumptions as `Assume` events, discharges only identifiers actually used (vacuous discharge otherwise), and produces a graph that is **then independently verified** by S3. Classical goals are reached by reductio when G4ip reports intuitionistic underivability but the truth-table oracle reports classical validity.

The separation is deliberate: G4ip *decides*, the synthesizer *produces a checkable certificate*, and S3 *trusts neither blindly*. On the benchmark of Section 8 the engine constructs and verifies $25/25$ theorems, intuitionistic and classical alike.

## 6.3. Verification and the oracle

For the propositional fragment the oracle is an in-process truth-table/SAT decision, so the reference implementation is end-to-end runnable with no external dependency. The architecture exposes the oracle as an interface: richer fragments dispatch to an SMT solver (with an Alethe/Carcara-checkable certificate [38,39]) or to an interactive prover (Lean/Coq/Isabelle [35,36,37]). The dichotomy of Theorem 5.6 tells the dispatcher which stratum suffices.

For the **computational** mathematics of the real corpus — whose steps assert arithmetic/algebraic (in)equalities rather than propositional inferences — we implement this interface concretely with an **SMT/CAS backend**: ground (variable-free) claims are decided by **Z3** over the rationals with an exact **SymPy** fallback for radicals; claims with free variables are decided **under the assumptions established by their premise steps** (a Z3 *entailment* query, with $\sqrt{}$ handled by auxiliary variables $s\ge0,\ s^2=k$, so nonlinear-real claims are reachable); only genuinely under-determined, ambiguous, or out-of-fragment claims are deferred rather than guessed; a **Lean** kernel backend discharges ground arithmetic by `decide`, and a **Lean + mathlib** tier discharges nonlinear-real/$\forall$-quantified obligations via `nlinarith`/`norm_num`, for highest-assurance cross-checking. Sections 8.10–8.12 report the measured behaviour: a near-perfect detection recall on corrupted arithmetic, a coverage rise from 21% to 35.6% via contextual entailment (premises and problem statement), and Lean–Z3 agreement on the ground fragment.

## 6.4. Diagnosis and localization

The well-formedness conditions induce a finite error taxonomy. Structural classes are decided by Algorithm 1 in linear time; the semantic class by the oracle.

| Class | Meaning | Detected by |
|-------|---------|-------------|
| E1 | missing/extra premise; conclusion mismatch (cond. 1–2) | structural |
| E2 | wrong open context / activation (cond. 4) | structural |
| E3 | discharge without an open witness, or discharged-but-still-open (cond. 5) | structural |
| E4 | well-formed but unsound inference (Definition 3.10) | oracle |
| E5 | illegal universal generalization (first-order scope) | structural (scope-augmented) |
| E6 | illegal existential elimination (first-order scope) | structural (scope-augmented) |

**Table 3.** The error taxonomy. E1–E3 are caught structurally and are the focus of the propositional implementation; E4 is semantic; E5–E6 are first-order scope errors handled by a scope-augmented checker (Section 9).

**Localization.** The diagnoser reports the *earliest* failing event in $\prec$-order and the **smallest failing sub-derivation** — its ancestor cone — so feedback points at the first place the argument goes wrong rather than at a cascade of downstream symptoms. On the synthetic corpus (Section 8) localization is exact (100%) for the structural classes.

## 6.5. The neuro-symbolic verify-and-repair loop

TCIH-Chat is designed to sit *behind* an LLM, not to replace it. In the verify-and-repair loop, the LLM proposes proof steps (a sketch, a tactic sequence, or a prose derivation); the ingester assembles them into a candidate TCIH; S3 verifies and S4 localizes any failure; and the localized, class-tagged feedback is returned to the LLM (or the user) as the next prompt. Because the feedback is *structural and precise* — "at this step, hypothesis $a$ is discharged but never opened" — it is exactly the signal the step-level-verification literature [13,14,15] and the repair literature [29] identify as effective, and it is produced with a correctness guarantee rather than by another fallible model.

## 6.6. Explanation at adjustable granularity

A verified proof is rendered as numbered natural-deduction steps showing each judgment and its justification (rule, premises, discharge). The granularity control uses the macro machinery of Section 4.3: a *detailed* view shows every base event; an *outline* view contracts provenance-marked blocks (e.g. a hypothetical-syllogism block) to single steps. This is the pedagogical surface a tutor needs — the same proof, shown coarsely to a beginner and finely to an advanced user — with the guarantee that the two views are inter-derivable.

Figure 2 shows an actual session (verbatim implementation output).

```text
∴ prove (A->B)->((B->C)->(A->C))
✓ Proved  ⊢ (A ⇒ B) ⇒ (B ⇒ C) ⇒ A ⇒ C   (intuitionistic; 8 steps, verified)
   1. h1:A ⇒ B ⊢ A ⇒ B              [assumption]
   2. h2:B ⇒ C ⊢ B ⇒ C              [assumption]
   3. h3:A ⊢ A                      [assumption]
   4. h1:A ⇒ B, h3:A ⊢ B            [modus ponens (⇒-elimination) from 1, 3]
   5. h1:A ⇒ B, h2:B ⇒ C, h3:A ⊢ C  [modus ponens (⇒-elimination) from 2, 4]
   6. h1:A ⇒ B, h2:B ⇒ C ⊢ A ⇒ C    [⇒-introduction from 5, discharge h3]
   7. h1:A ⇒ B ⊢ (B ⇒ C) ⇒ A ⇒ C    [⇒-introduction from 6, discharge h2]
   8. · ⊢ (A ⇒ B) ⇒ (B ⇒ C) ⇒ A ⇒ C [⇒-introduction from 7, discharge h1]

∴ valid ~~A -> A
  intuitionistic: False;  classical: True
```

**Figure 2.** A verbatim TCIH-Chat session: an intuitionistic proof, automatically constructed and verified, with explicit contexts and discharge; and a validity query distinguishing intuitionistic from classical provability.

## 6.7. Implementation and reproducibility

The reference implementation is a dependency-free Python package (`tcih/`): `formula`, `model`, `rules`, `check`, `oracle`, `fold`, `granularity`, `prover`, `search`, `diagnose`, `chatbot`, a rule-classifying corpus parser `nl_parser`, and a `gallery` of corrected case studies. A regression suite contains one machine-checked test per corrected result (Table 1); `run_artifacts.py` regenerates the formal results of Section 8 into `artifacts/results.json`; and `corpus_stats.py` / `run_corpus_eval.py` regenerate the real-corpus distributions and the upgraded-parser evaluation of §8.8–8.9 into `artifacts/corpus_stats.json` and `artifacts/corpus_eval.json`. For reproducibility the released commit is tagged (release `v1.0.0`) and accompanied by the Python version and a dependency lock; the data-and-code-availability statement (end of paper) is written to be consistent with that artefact, removing the contradiction noted in review.
