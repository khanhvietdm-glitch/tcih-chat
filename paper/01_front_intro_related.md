# TCIH-Chat: A Typed Event-Hypergraph Framework and Conversational Assistant for Automated Construction and Structural Diagnosis of Mathematical Proofs

**Nguyen Truong Thang¹, Truong Thi Minh Ngoc¹, Le Thi Thuy Giang¹,², Vuong Quang Phuong¹, Do Thi Loan¹, Pham Van Khanh¹,\***

*¹ Institute of Information Technology (IOIT), Vietnam Academy of Science and Technology (VAST), Hanoi, Vietnam.*
*² Graduate University of Science and Technology (GUST), Vietnam Academy of Science and Technology (VAST), Hanoi, Vietnam.*

*\* Corresponding author: Pham Van Khanh (khanhvietdm@gmail.com).*

---

## Abstract

**Problem.** Large language models (LLMs) now produce fluent mathematical arguments, but their proofs fail in two qualitatively different ways: *structural* failures, in which the skeleton of the argument is malformed (a premise is missing, a hypothesis is used outside the scope in which it was discharged), and *semantic* failures, in which every step is well-formed but one inference is not a valid entailment. Existing tools — proof assistants, SAT/SMT back-ends, and benchmark scorers — either reject an argument wholesale or report a single pass/fail number; none separates these failure modes or localizes them in a way that an interactive tutor or an autoformalization pipeline can act on. **System.** We present *TCIH-Chat*, a neuro-symbolic mathematics proof-assistant chatbot whose symbolic core is a *typed contextual inference hypergraph* (TCIH): a proof is represented as an ordered event-hypergraph over labelled judgments, in which assumptions carry identifiers and discharge is an event rather than a vertex flag. On this core the assistant (i) *constructs* proofs automatically with a terminating intuitionistic decision procedure and a natural-deduction synthesizer, (ii) *verifies* every proof it presents with a linear-time structural checker backed by a semantic oracle, (iii) *diagnoses* student- or LLM-authored proofs, classifying each error into a six-class taxonomy and localizing it to the smallest failing sub-derivation, and (iv) *explains* proofs at an adjustable granularity. **Theory.** We give corrected proofs of four results that make this pipeline sound: an order- and context-preserving folding theorem (with a rank-function criterion for quotient acyclicity), a granularity theorem recast as provenance-marked macro-elimination, a stratified structural/semantic complexity dichotomy with an explicit input-size model, and cut-elimination as semantic confluence after encoding. **Evaluation and results.** On a 25-theorem propositional benchmark the assistant constructs and independently verifies **25/25** proofs; on a synthetic ground-truth error corpus it attains **macro-averaged recall 0.955** with a **0.0 false-rejection rate** on correct proofs and **100%** localization for the structural error classes; structural checking is empirically **linear** in the encoded input size (constant µs-per-node across three orders of magnitude); and on a corpus of **211,922** real solution proofs (1.84M nodes) an upgraded rule-classifying parser eliminates the legacy parser's **57.7%** spurious sequential edges and supports structural error detection at **recall 1.0** with **zero false rejection** and exact localization on real proof structures, while an **SMT/CAS semantic oracle** (Z3 + SymPy) decides the corpus arithmetic and detects corrupted equalities at recall **0.9998** — with contextual entailment under premise- and problem-statement assumptions lifting decidable coverage from 21% to **35.6%** (including nonlinear/$\sqrt{}$ claims), and a **Lean 4 kernel backend agreeing 100%** with Z3 on the ground fragment, extended by a **Lean + mathlib** tier that discharges nonlinear-real inequalities (AM–GM, $\sqrt 6-\sqrt 2>0$) by kernel proof. A reference implementation — a dependency-free symbolic core plus the SMT/Lean oracle stack — a regression suite (one test per corrected result), and deterministic artefact generators accompany the paper.

**Keywords:** automated theorem proving; neuro-symbolic AI; proof verification; natural deduction; inference hypergraph; LLM proof diagnosis; intelligent tutoring; mathematics chatbot.

---

# 1. Introduction

## 1.1. Motivation: trustworthy automated and assisted proving

A mathematical proof is rarely a linear chain. Even the schoolbook inference *from $P$ and $P \Rightarrow Q$, infer $Q$* requires two premises to act **simultaneously**; in any argument of size, lemmas are reused, hypotheses are temporarily assumed and later discharged, and the same propositional content recurs under different open assumptions while playing different logical roles. This combinatorial structure is exactly what a *graph* captures and a *sequence* does not, a view as old as Gentzen's derivation trees [1] and Prawitz's normalization [2] and central to proof nets [3], proof DAGs [4], and the AND/OR search graphs of automated reasoning [5].

The practical urgency of getting that structure right has changed. Large language models now generate proofs at scale — Minerva-style solvers, the Lean-based provers, AlphaGeometry and AlphaProof, and the DeepSeek-Prover line [6,7,8,9,10,11] — and a parallel literature shows that their reasoning must be *checked*, because models cannot reliably self-correct without an external signal [12], and because step-level (process) verification substantially outperforms outcome-level scoring [13,14,15]. Yet the dominant evaluation still reports a single number: the fraction of theorems closed. For an *expert system* that has to help a student, repair an autoformalization, or flag a suspect lemma, a single number is the wrong output. The system needs to know **where** and **how** an argument breaks.

We take the position that the two ways a proof breaks are fundamentally different and should be handled by different machinery:

- a **structural** failure is a defect of the proof *skeleton* — a missing premise, a context that does not match the inference rule, a hypothesis discharged that was never opened, or a discharged hypothesis reused as if still live. These are decidable in polynomial time, independently of the background logic.
- a **semantic** failure is a single inference that is perfectly well-formed but is not a valid entailment. Its detection inherits the complexity of the background logic, from linear (Horn) to undecidable (first-order validity).

A system built on this dichotomy can be fast and certain about the structural layer and explicit about delegating the semantic layer to a SAT/SMT solver or an interactive theorem prover. This paper develops that system, *TCIH-Chat*, together with the corrected formal model it requires.

## 1.2. Why a new representation is needed

Three phenomena force design choices that ordinary proof DAGs do not record, and getting any of them wrong silently produces an object that *looks* like a derivation but is not one.

**(a) Assumption identity and discharge.** In a proof of $A \Rightarrow A$ the hypothesis $A$ is opened, used, and then discharged by implication-introduction. If a proof graph identifies two occurrences of $A$ purely by propositional content, it can merge an *open* hypothesis with a *discharged* one, or merge an inner hypothesis with an unrelated outer assumption of the same content. A correct model must distinguish *occurrences*, not just contents.

**(b) Schema versus instance.** A rule such as "add the same quantity to both sides" is a *schema* parameterized by a substitution; conflating two instances with different substitutions conflates two different inferences.

**(c) Granularity.** A lemma can appear as a single high-level step or as its full expansion; a useful theory of proof graphs must say precisely how quantitative invariants behave under such refinement.

A first version of this framework (the manuscript that precedes the present one) proposed a vertex labelled by a quadruple *(formula, open context as a set of formulas, sort, discharge flag)*. A careful review identified that this design is internally inconsistent on exactly the points above: discharge was defined as a subset of the premises, although a discharged hypothesis is not a peer premise; the context was a *set of formula contents*, so two hypotheses with the same content could not be told apart; the discharge flag was used as a time-varying state but stored in a static vertex label; and, as a consequence, the framework could not even represent the derivation of $A \Rightarrow A$ from no assumptions. Several downstream theorems inherited the defect, including a folding theorem, a quotient-DAG proposition (which is in fact false as stated), a granularity theorem stated too strongly, an A\* heuristic-correction rule that does not restore admissibility, and a case study mislabelled as a logical equivalence that holds only classically.

Rather than patch these locally, we redesign the core. The redesign is not ad hoc: it is the standard move of treating a vertex as a **labelled judgment** and a proof as an **ordered event structure**, and every one of the affected results is then re-stated correctly and re-proved. Crucially, the redesign is also *executable*: we provide a reference implementation whose regression suite contains one machine-checked test per correction, so the coherence of the new model is not merely argued but run.

## 1.3. Contributions

1. **A corrected formal model (Section 3).** A TCIH is an ordered event-hypergraph $G=(V,E,\lambda_V,\lambda_E,\prec)$. A vertex is a labelled judgment $v=(\mathrm{id}_v,\ \Gamma_v \vdash \varphi_v,\ \tau_v)$ with a labelled context $\Gamma_v : \mathrm{AssumptionID} \rightharpoonup \mathrm{Form}_\Sigma$; an event is $e=(S_e,t_e,R[\sigma_e],D_e,\mathrm{prov}_e)$ where $D_e$ is the set of assumption identifiers discharged *at that event*. Open/discharged status is derived from the event history; there is no mutable vertex flag. Assumption-opening is a first-class event, so $\vdash A\Rightarrow A$ is representable.

2. **Corrected theory (Section 4).** We prove (i) soundness and a syntactic relative-completeness statement; (ii) an **Order- and Context-Preserving Folding Theorem**, with a concrete witness that content-only folding is unsound and a **rank-function** criterion that repairs the false antichain-quotient proposition of the earlier draft; (iii) a **Granularity Theorem** repositioned as provenance-marked macro-elimination, with an exact length law, a corrected length-difference corollary, and an explicit matching family; and (iv) **cut-elimination as semantic confluence** after a typed-$\lambda$ encoding, with the over-strong "graph-level confluence" claim downgraded to what the encoding actually supports.

3. **Algorithms and a stratified complexity dichotomy (Section 5).** An explicit encoded-input-size model $N$; a linear-time `StructuralCheck` that *verifies a supplied substitution* (kept separate from unification search); the Horn forward-chaining specialization where closure, shortest path and proof length genuinely coincide; and a corrected A\* treatment using a **certified lower bound** (with a worked counterexample to the previously proposed $\min(h,b)$ rule).

4. **TCIH-Chat: a neuro-symbolic proof-assistant chatbot (Section 6).** A terminating intuitionistic decision procedure (Dyckhoff's G4ip) and a natural-deduction synthesizer that **emits derivations the verifier checks**, a classical mode via reductio, an adjustable-granularity explainer, and a verify-and-repair loop in which an LLM may propose steps that the symbolic core validates and localizes.

5. **An evaluation protocol and measured results (Sections 7–8).** A reproducible protocol (corpus, baselines, metrics, ablations, robustness), with **measured** results on a 25-theorem benchmark (25/25 constructed and verified), a synthetic ground-truth error corpus (macro-recall 0.955, false-rejection 0.0, 100% structural localization), linear-in-$N$ scaling, and a real 211,922-proof corpus; plus a **rule-classifying parser** that, on that corpus, eliminates the legacy parser's 57.7% spurious sequential edges (replacing them with hypothesis-rooted, value-dependent structure) and supports a measured structural error-detection evaluation (recall 1.0, 0.0 false rejection, exact localization) on real proof structures. An **SMT/CAS/Lean oracle stack** then decides the corpus arithmetic (the E4 stratum): Z3 + SymPy give a $0.9998$ detection recall on corrupted equalities with sound deferral; contextual entailment under premise- and problem-statement assumptions lifts decidable coverage from 21% to 35.6% (including nonlinear/$\sqrt{}$ claims); a Lean 4 kernel backend cross-validates the ground fragment with 100% agreement; and a Lean + mathlib tier discharges nonlinear-real/$\forall$-quantified obligations (e.g. AM–GM) by kernel proof. Corpus-scale mathlib runs and the autoformalization of geometry word problems, together with detection of *naturally occurring* errors over an annotated logical-fragment corpus, are identified as the outstanding tasks.

6. **A dependency-free reference implementation** with a regression suite (one test per corrected result) and a deterministic artefact generator.

Throughout, we are explicit about scope: the formal guarantees and the implemented prover concern **propositional** natural deduction (intuitionistic, with a classical mode); first-order and equality reasoning enter through the semantic oracle and are discussed as extensions (Section 9).

## 1.4. What changed relative to the precursor manuscript

For readers familiar with the earlier draft, Table 1 indexes each substantive correction to where it is addressed and, where applicable, to the test that pins it down in the implementation.

| # | Issue in the precursor | Resolution in this paper | Test |
|---|------------------------|--------------------------|------|
| 1 | Discharge defined as a subset of premises | Discharge acts on labelled assumptions, separate from premises (§3.2) | — |
| 2 | Context = set of formula contents | Context = labelled map $\mathrm{AssumptionID}\rightharpoonup\mathrm{Form}$ (§3.1) | model |
| 3 | Discharge flag as mutable vertex state | No flag; status derived from events and order $\prec$ (§3.3) | model |
| 4 | $\vdash A\Rightarrow A$ unrepresentable | Assumption-opening is an event (§3.3, Ex. 4.2) | `a_imp_a` |
| 5 | Folding theorem incomplete | Order- and Context-Preserving Folding Thm (§4.2) | fold |
| 6 | Quotient-DAG proposition false | Rank-function criterion + antichain counterexample (§4.2) | antichain |
| 7 | Granularity theorem overstated | Macro-elimination with provenance; exact law (§4.3) | granularity |
| 8 | Cut-elimination confluence gap | Semantic confluence after encoding (§4.4) | — |
| 9 | Complexity without input-size model | Explicit $N$; verify-$\sigma$ vs. search split (§5.1) | scaling |
| 10 | A\* $\min(h,b)$ correction wrong | Certified lower bound; counterexample (§5.4) | astar |
| 11 | "De Morgan equivalence" not valid | Replaced by the intuitionistic equivalence (§4, App. B) | ipc |
| 12 | No evaluated system | TCIH-Chat with protocol and results (§6–8) | — |

**Table 1.** Index of corrections. The "Test" column names the regression test in the reference implementation that exercises the fix.

---

# 2. Background and Related Work

## 2.1. Proof graphs, nets, and compression

That a natural-deduction tree can be folded into a directed acyclic graph by sharing repeated subproofs goes back to Statman [16] and is standard in proof complexity [17] and proof compression [18]. Girard's proof nets [3], with the Danos–Regnier correctness criterion [19], are the most developed "proof as graph" theory, though tuned to linear logic's resource sensitivity. We work in ordinary (intuitionistic/classical) natural deduction and use *labelled* judgments as vertices, so that sharing is governed by an explicit folding criterion rather than by equality of propositional content; Section 4.2 exhibits a concrete derivation on which content-only sharing is unsound. The Curry–Howard reading of proofs as typed terms [20,21] underlies our cut-elimination treatment. Equality saturation and e-graphs [22] are a dual graph-rewriting technology — adding alternative derivations to one graph rather than asking what is preserved under refinement — and a natural target for future equational extensions.

## 2.2. Proof representation for learning and search

Graph encodings of formulas and proof states have been used to drive premise selection and tactic prediction with graph neural networks [23,24], including recent applied-AI work on simplified formula graphs [25]. These systems learn *guidance*; our hypergraph is instead a *verification and diagnosis* substrate with correctness guarantees, complementary to learned guidance. The same distinction separates us from search-level systems: Dowling and Gallier's linear-time Horn algorithm [26] is imported as the Horn specialization of our framework, and A\* with admissible/consistent heuristics [27,28] is the search layer whose admissibility caveats we make precise.

## 2.3. LLM theorem proving, autoformalization, and step-level verification

The neural theorem-proving line — GPT-f [6], autoformalization [7], Draft-Sketch-Prove [8], LeanDojo [9], Baldur [29], AlphaGeometry [10], AlphaProof [11], DeepSeek-Prover [30,31], Lean Copilot [32], Lean-STaR [33] — has made proof *generation* powerful but has sharpened the need for fine-grained *checking*. "Let's Verify Step by Step" [13], Math-Shepherd [14], and ProcessBench [15] establish that step-level verification and error localization are the right granularity, while [12] shows external feedback is necessary. A survey of the area is [34]. Our contribution sits on the verification side: a logic-grounded, polynomial-time structural checker plus a semantic oracle, producing exactly the per-step, localized signal these works call for. Baldur's whole-proof *repair* loop [29] is the closest analogue to our verify-and-repair design, but it operates inside one prover's tactic language, whereas TCIH-Chat's checker is foundation-independent.

## 2.4. Proof assistants and proof-exchange infrastructure

Lean 4 [35], Coq/Rocq [36], and Isabelle [37], and proof-exchange/checking formats such as Alethe with its checker Carcara [38,39], DPLL(T) proofs [40], DRAT certificates [41], and the $\lambda\Pi$-calculus-modulo interoperability route [42], all fix a foundation and design a syntax expressive enough to record proofs in it. A TCIH is deliberately *foundation-independent*: it is a structural object whose semantic validity is delegated to a chosen back-end, and our complexity dichotomy quantifies the cost of that delegation. TCIH-Chat is therefore compatible with, not competitive with, these systems; any of them can serve as its semantic oracle.

## 2.5. Intelligent tutoring and feedback on student proofs

The work closest in *application* is automated feedback for student-constructed proofs: LogAx generates hints for Hilbert-style proofs using a derivation multigraph and reports covering about 80% of student mistakes [43,44], building on a rewrite-strategy feedback framework [45]; recent systems pair an LLM tutor with a Lean back-end for student proofs [46], and an ITS study quantifies LLM stepwise accuracy and hint quality on propositional-logic problems [47]. These systems are mostly tied to one proof style or one back-end. TCIH-Chat contributes a representation-level account — assumption-scope-aware structural diagnosis with localization — that is independent of the proof style and that cleanly separates the structural feedback (which it guarantees) from the semantic feedback (which it delegates).

## 2.6. Research gap

Three gaps remain. (i) *Representation*: existing proof-graph models either omit assumption scope and discharge or encode them in a way (set-valued contexts, mutable flags) that does not survive sharing, so the very operation that makes proof graphs useful — folding — is unsound or unverified. (ii) *Dichotomy*: the structural-vs-semantic boundary that should govern an expert system for proofs is rarely made precise, leading to over-strong "polynomial-time error detection" or "ML-heuristics-justified optimality" claims. (iii) *System*: there is no evaluated, foundation-independent system that constructs, verifies, diagnoses, and explains proofs at the level of granularity a tutor or an autoformalization pipeline needs. This paper addresses all three with a corrected model, a stratified complexity account, and the TCIH-Chat system with a reproducible evaluation.
