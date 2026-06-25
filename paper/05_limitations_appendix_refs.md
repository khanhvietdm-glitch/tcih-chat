# 9. Limitations and Threats to Validity

**Scope of the formal guarantees and the prover.** The theorems of Section 4 and the implemented prover concern *propositional* natural deduction (intuitionistic, with a classical reductio mode). First-order quantifier and equality reasoning enter only through the semantic oracle; the scope-sensitive error classes E5 (illegal universal generalization) and E6 (illegal existential elimination) require a scope-augmented structural checker that records the free variables in force at each vertex. The design accommodates this (the vertex already carries a context), but it is not implemented or evaluated here.

**Cut-elimination.** Theorem 4.7 covers the simply-typed implicational–conjunctive fragment and claims only semantic confluence after encoding and sharing erasure. Graph-level confluence — equivalently, injectivity or full abstraction of the encoding modulo a precisely defined equivalence — is open, as is the extension to disjunction, falsum, quantifiers, and dependent types.

**Evaluation.** Error detection is measured on three grounds: a synthetic propositional corpus (Tables 7–8), real corpus proof *structures* with injected faults (Tables 12–13), and the real corpus *arithmetic* via the SMT/CAS oracle (Table 14). The injected-fault experiments use controlled labels rather than wild errors, so their distribution need not match human/LLM mistakes. The SMT/CAS oracle decides only the *ground arithmetic* fragment ($\approx$21% of steps), deferring — soundly — on symbolic, transcendental, and percent claims, and a small residual LaTeX-parsing false-positive rate remains on the raw flags (hence we headline the injection-detection recall, $0.9998$, not the flag count). The Lean backend is real and run (§8.12): core Lean kernel-checks the *ground* arithmetic fragment via `by decide` (100% agreement with Z3), and a provisioned **Lean + mathlib** tier discharges representative nonlinear-real and $\forall$-quantified obligations (AM–GM, completed squares, $\sqrt 6-\sqrt 2>0$) via `nlinarith`/`norm_num` while refusing a false goal. Two things remain out of scope: running the mathlib tier at *corpus scale* (each query loads mathlib, $\approx$30–60 s), and checking *geometry/word-problem* semantics, which would require **autoformalizing** prose into mathlib statements — an autoformalization step we do not perform. Two gaps are therefore deliberately not claimed: *non-arithmetic semantic* validity at scale (geometry, symbolic inequalities beyond what contextual Z3 reaches, higher-order content), and detection of *naturally occurring* errors on an annotated natural-deduction corpus of human/LLM proofs (the remaining D5 task), which needs proofs in a logical fragment with first-error annotation. The propositional oracle is a truth-table/SAT decision, exponential in the worst case; at scale it should be replaced by a full SAT/SMT back-end. Reported wall-clock times are machine-dependent; only the flatness of µs-per-node (the $O(N)$ claim) is portable.

**Granularity and proof identity.** Theorem 4.6 is macro-rule elimination with provenance, not arbitrary rule-library refinement; an information-theoretic version of the length law (relating the length difference to the complexity of the substituted derivation) is conjectural. The contracted-minimal-form equivalence suggests a notion of proof identity whose relationship to $\beta\eta$-equivalence and to Lévy's family relation is left open. Equality up to congruence is treated as an uninterpreted predicate rather than internalized via e-graphs.

**Parser.** The prose ingester targets *structured* step-by-step solutions; general natural-language proof parsing is out of scope and is the natural place for an LLM front-end, with the symbolic core as the verifier (Section 6.5).

# 10. Conclusion

We have rebuilt the typed contextual inference hypergraph on a correct foundation — labelled-judgment vertices and an ordered event-hypergraph in which discharge is an event, not a vertex flag — and re-proved, in corrected form, the four results that make it usable: order- and context-preserving folding with a rank criterion for quotient acyclicity, granularity as provenance-marked macro-elimination with an exact length law, a stratified structural/semantic complexity dichotomy over an explicit input-size model, and cut-elimination as semantic confluence. On this foundation we built TCIH-Chat, a neuro-symbolic mathematics proof-assistant chatbot that constructs proofs automatically, verifies everything it presents, diagnoses and localizes errors in human- and LLM-authored proofs, and explains proofs at adjustable granularity. The system constructs and verifies all 25 benchmark theorems, detects the structural error classes with perfect recall and localization and zero false rejection on a ground-truth corpus, and — in the ablation the design must answer — shows that removing the labelled context and discharge identifiers makes scope and discharge errors undetectable. The complete reference implementation, the regression suite that pins each correction, and the deterministic artefact generator make every claim reproducible.

The framework's natural role is as the trusted, foundation-independent verifier behind a fallible generator: an LLM proposes, the hypergraph disposes — checking, localizing, and explaining with a guarantee the generator cannot provide on its own. Closing the loop on real human and LLM corpora, extending the structural guarantees to first-order scope, and connecting the semantic oracle to SMT and interactive-prover back-ends are the next steps.

## Declarations

**Funding.** This research was supported by the initial scientific and technological project of the Institute of Information Technology (IOIT), Vietnam Academy of Science and Technology (VAST), "Training a large language model integrating formal logical thinking for solving general mathematics problems," grant number NVKN02.05/26-27.

**Conflict of interest.** The authors declare no conflict of interest.

**CRediT author statement.** *Pham Van Khanh:* Conceptualization, Methodology, Software, Formal analysis, Writing – original draft. *Nguyen Truong Thang:* Conceptualization, Supervision, Writing – review & editing. *Truong Thi Minh Ngoc:* Validation, Investigation. *Le Thi Thuy Giang:* Software, Data curation. *Vuong Quang Phuong:* Investigation, Visualization. *Do Thi Loan:* Data curation, Writing – review & editing. (To be confirmed by the authors.)

**Data and code availability.** The complete system — the `tcih` package (model, linear-time structural checker, G4ip prover and ND synthesizer, folding, granularity, search, the SMT/CAS and Lean oracle backends, diagnosis, the conversational assistant, and the rule-classifying corpus parser), the regression suite, the artefact generators, the figure scripts, and the manuscript sources — is open-source under the MIT licence at **https://github.com/khanhvietdm-glitch/tcih-chat**. Running `python -m pytest` reproduces the machine-checked results (one test per corrected theorem); the `run_*.py` scripts regenerate every measured number in Section 8 into `artifacts/*.json`. The proof-graph corpus (D4) is provided **structure-only** — node kinds, hyperedge incidences, edge-provenance types, and per-proof statistics, with all natural-language solution text removed (`strip_corpus.py`) to respect the source dataset's licence — as an in-repository sample (`data/sample/`) and a full release asset (`corpus_full_structure_only.tar.gz`); this suffices to reproduce the structural results (Tables 10–13). Reproducing the semantic-oracle results (Tables 14–16) additionally requires the original solution text, available from the authors on request under the source licence. Datasets D1–D3 are generated by the released code. The tagged release **v1.0.0** of the repository above — with the full structure-only corpus attached as a release asset — is the version of record for the results reported here. This statement supersedes any earlier statement.

---

# Appendix A. Selected proofs

**A.1. Folding sufficiency (Theorem 4.4(a)).** Let $f$ be label-preserving with acyclic quotient. Conditions 1–3 of Definition 3.7 reference only contents, sorts and rule labels, all preserved by $f$. For condition 4, identified source vertices have identical labelled contexts, so $\biguplus_s\Gamma_s$ is unchanged and remains defined, and removing $D_e$ commutes with $f$; hence $\Gamma_{t_e}$ matches the activation result in the quotient. For condition 5, each $a\in D_e$ retains its binding (contexts are preserved) and its absence from $\Gamma_{t_e}$. Distinct source incidences may map to one vertex, but incidence multiplicities in $S_e$ and the discharge set $D_e$ are carried by the event label, which $f$ preserves; structurally identical justifications merge, keeping unique justification. Semantic validity depends only on $R[\sigma_e]$, unchanged. Acyclicity holds by hypothesis (certified by the rank function of Proposition 4.5). $\square$

**A.2. Rank certificate (Proposition 4.5, sufficiency).** Suppose $\rho:V\to\mathbb N$ is constant on $\sim$-classes and strictly increasing along edges. A quotient edge $[u]\to[w]$ lifts to an edge $u'\to w'$ with $u'\sim u$, $w'\sim w$, so $\rho([u])=\rho(u')<\rho(w')=\rho([w])$. Thus $\rho$ descends to a strictly increasing function on the quotient, which therefore has no directed cycle. The longest-chain rank of the original DAG, when constant on classes, is such a $\rho$; the implementation tests quotient acyclicity directly and returns this rank as a certificate. $\square$

**A.3. Granularity length law (Theorem 4.6(iii)).** Expanding one $r$-event deletes a single event and inserts the $|D_r|$ events of one $D_r$-copy, the last of which targets the original macro target; the net change is $|D_r|-1$. Distinct macro-events expand into vertex-disjoint blocks (fresh identifiers, provenance-tagged), so the changes sum, giving $|\mathrm{expand}(G)|=|G|+k_r(G)(|D_r|-1)$. Expanding a length-minimal $\mathcal R$-derivation yields an $\mathcal R'$-derivation of length $|G_{\min}|+k_r(G_{\min})(|D_r|-1)$, hence the constructive upper bound; the HS-chain family of Section 8.3 attains it. $\square$

# Appendix B. Corrected case studies

**B.1. $\vdash A\Rightarrow A$ (review issue 4.5).** Open $a{:}A\vdash A$ by `Assume`; apply $\Rightarrow\!I$ discharging $a$ to obtain $\vdash A\Rightarrow A$. Two vertices, two events; well-formed. The precursor could not express this because it lacked an assumption-opening event.

**B.2. The De Morgan equivalence (review issue 4.13).** The precursor's "De Morgan equivalence" $\neg(A\wedge B)\vdash\neg A\vee\neg B$ is *not* intuitionistically valid (the decision procedure G4ip reports it underivable; the truth-table oracle confirms it is classically valid). We use instead the genuine intuitionistic equivalence $\neg(A\vee B)\dashv\vdash(\neg A\wedge\neg B)$. The forward direction, as constructed and verified by the assistant:

```text
✓ Proved  ¬(A ∨ B) ⊢ ¬A ∧ ¬B   (intuitionistic; 10 steps, verified)
   1. g0:¬(A ∨ B) ⊢ ¬(A ∨ B)             [assumption]
   2. h1:A ⊢ A                           [assumption]
   3. h1:A ⊢ A ∨ B                       [∨-introduction (left) from 2]
   4. g0:¬(A ∨ B), h1:A ⊢ ⊥              [¬-elimination from 3, 1]
   5. g0:¬(A ∨ B) ⊢ ¬A                   [¬-introduction from 4, discharge h1]
   6. h2:B ⊢ B                           [assumption]
   7. h2:B ⊢ A ∨ B                       [∨-introduction (right) from 6]
   8. g0:¬(A ∨ B), h2:B ⊢ ⊥              [¬-elimination from 7, 1]
   9. g0:¬(A ∨ B) ⊢ ¬B                   [¬-introduction from 8, discharge h2]
  10. g0:¬(A ∨ B) ⊢ ¬A ∧ ¬B              [∧-introduction from 5, 9]
```

**B.3. The folding witness ($(A\Rightarrow A)\wedge A$ from $\{A\}$).** The derivation opens an inner hypothesis $a_{\mathrm{in}}{:}A$ (discharged by $\Rightarrow\!I$ to give $A\Rightarrow A$) and uses an outer assumption $a_{\mathrm{out}}{:}A$ that stays open, then conjoins. Content-only folding identifies $a_{\mathrm{in}}$ with $a_{\mathrm{out}}$ and is rejected by the verifier (activation failure at the $\Rightarrow\!I$ event and a discharge-without-witness); label-preserving folding leaves them distinct. This is the executable witness for Theorem 4.4(b).

# Appendix C. Example diagnosis session

A faulty proof (here a proof of $\neg P$ from $\{P\Rightarrow Q,\neg Q\}$ with a discharge error injected) is diagnosed and localized:

```text
(injected E3 at e4)
✗ Problems found:
   • [E3] at e4: discharged id ghost is not open in any source context
   ↳ first failure at e4; smallest failing sub-derivation: events ['e1', 'e3', 'e4']
```

The assistant reports the error class (E3, a discharge without an open witness), the offending event, and the smallest sub-derivation that exposes it — the precise, localized feedback an LLM-repair loop or a student tutor can act on.

# Appendix D. Example real corpus proof graphs

The following figures render real corpus solutions as TCIH event-hypergraphs using the **upgraded parser** of §8.9: the problem hypothesis (green) and derived steps (blue) are connected through *classified* rule events (orange, labelled by inferred class — Comp, Apply, Concl, … — and arity $\wedge$), with **value-dependency edges** (solid blue) distinguished from **hypothesis-attached edges** (dashed grey). They illustrate, on real data, the faithful structure that replaces the legacy parser's sequential-fallback chains (§8.8–8.9): parallel computation steps root at the hypothesis, while aggregation steps (e.g. a running total) are genuinely multi-source. These are reproducible via `make_corpus_figures.py`.

![**Figure 5.** Arithmetic — multi-source aggregation. The total-cost step is a multi-source event ($\wedge=2$) drawing value-dependency edges (solid blue) from the item-cost steps, while the per-item steps root at the hypothesis (dashed grey). This is the structure the legacy parser misrepresented as a sequential chain.](figures/corpus_number_theory_arithmetic_1.png){width=100%}

![**Figure 6.** Algebra — a short computational chain, with value dependencies linking each result to the step that consumes it.](figures/corpus_algebra_1.png){width=100%}

![**Figure 7.** Calculus / analysis — a deeper proof in which several steps carry genuine value dependencies rather than mere sequential adjacency.](figures/corpus_calculus_analysis_1.png){width=100%}

![**Figure 8.** Propositional logic — parallel derivations rooted at the hypothesis; the legacy parser (§8.8) chained these sequentially, whereas the upgraded parser attaches each to the hypothesis it actually depends on.](figures/corpus_logic_foundations.png){width=100%}

---

# References

[1] G. Gentzen. Untersuchungen über das logische Schließen. I & II. *Mathematische Zeitschrift*, 39:176–210, 405–431, 1935.

[2] D. Prawitz. *Natural Deduction: A Proof-Theoretical Study*. Almqvist & Wiksell, 1965 (Dover reprint, 2006).

[3] J.-Y. Girard. Linear logic. *Theoretical Computer Science*, 50(1):1–101, 1987.

[4] R. Statman. *Structural Complexity of Proofs*. PhD thesis, Stanford University, 1974.

[5] N. J. Nilsson. *Problem-Solving Methods in Artificial Intelligence*. McGraw-Hill, 1971.

[6] S. Polu and I. Sutskever. Generative language modeling for automated theorem proving. arXiv:2009.03393, 2020.

[7] Y. Wu, A. Q. Jiang, W. Li, M. N. Rabe, C. Staats, M. Jamnik, and C. Szegedy. Autoformalization with large language models. In *NeurIPS*, 2022.

[8] A. Q. Jiang, S. Welleck, J. P. Zhou, et al. Draft, sketch, and prove: Guiding formal theorem provers with informal proofs. In *ICLR*, 2023.

[9] K. Yang, A. M. Swope, A. Gu, et al. LeanDojo: Theorem proving with retrieval-augmented language models. In *NeurIPS*, 2023.

[10] T. H. Trinh, Y. Wu, Q. V. Le, H. He, and T. Luong. Solving olympiad geometry without human demonstrations. *Nature*, 625:476–482, 2024.

[11] T. Hubert, R. S. Mehta, L. Sartran, et al. (Google DeepMind). Olympiad-level formal mathematical reasoning with reinforcement learning (AlphaProof). *Nature*, 2025.

[12] J. Huang, X. Chen, S. Mishra, et al. Large language models cannot self-correct reasoning yet. In *ICLR*, 2024.

[13] H. Lightman, V. Kosaraju, Y. Burda, et al. Let's verify step by step. In *ICLR*, 2024.

[14] P. Wang, L. Li, Z. Shao, et al. Math-Shepherd: Verify and reinforce LLMs step-by-step without human annotations. In *ACL*, 9426–9439, 2024.

[15] C. Zheng, Z. Zhang, B. Zhang, et al. ProcessBench: Identifying process errors in mathematical reasoning. arXiv:2412.06559, 2024.

[16] R. Statman. Bounds for proof-search and speed-up in the predicate calculus. *Annals of Mathematical Logic*, 15:225–287, 1978.

[17] S. R. Buss (ed.). *Handbook of Proof Theory*. Elsevier, 1998.

[18] J. Boudou, A. Fellner, and B. Woltzenlogel Paleo. Skeptik: A proof-compression system. In *IJCAR*, LNCS 8562, 374–380, 2014.

[19] V. Danos and L. Regnier. The structure of multiplicatives. *Archive for Mathematical Logic*, 28:181–203, 1989.

[20] M. H. Sørensen and P. Urzyczyn. *Lectures on the Curry–Howard Isomorphism*. Elsevier, 2006.

[21] P. Wadler. Propositions as types. *Communications of the ACM*, 58(12):75–84, 2015.

[22] M. Willsey, C. Nandi, Y. R. Wang, O. Flatt, Z. Tatlock, and P. Panchekha. egg: Fast and extensible equality saturation. *PACMPL* 5(POPL), Article 23, 2021.

[23] A. Paliwal, S. Loos, M. Rabe, K. Bansal, and C. Szegedy. Graph representations for higher-order logic and theorem proving. In *AAAI*, 34(3):2967–2974, 2020.

[24] M. Wang, Y. Tang, J. Wang, and J. Deng. Premise selection for theorem proving by deep graph embedding. In *NeurIPS*, 2017.

[25] Integrating a simplified formula graph representation into a graph neural network model for premise selection. *Applied Soft Computing*, 2025. (DOI 10.1016/j.asoc.2025.113318.)

[26] W. F. Dowling and J. H. Gallier. Linear-time algorithms for testing the satisfiability of propositional Horn formulae. *Journal of Logic Programming*, 1(3):267–284, 1984.

[27] P. E. Hart, N. J. Nilsson, and B. Raphael. A formal basis for the heuristic determination of minimum cost paths. *IEEE Transactions on Systems Science and Cybernetics*, 4(2):100–107, 1968.

[28] S. Russell and P. Norvig. *Artificial Intelligence: A Modern Approach*, 4th ed. Pearson, 2021.

[29] E. First, M. N. Rabe, T. Ringer, and Y. Brun. Baldur: Whole-proof generation and repair with large language models. In *ESEC/FSE*, 2023.

[30] H. Xin, Z. Z. Ren, J. Song, et al. (DeepSeek-AI). DeepSeek-Prover-V1.5: Harnessing proof-assistant feedback for RL and Monte-Carlo tree search. arXiv:2408.08152, 2024.

[31] Z. Z. Ren, Z. Shao, J. Song, et al. (DeepSeek-AI). DeepSeek-Prover-V2: Advancing formal mathematical reasoning via RL for subgoal decomposition. arXiv:2504.21801, 2025.

[32] P. Song, K. Yang, and A. Anandkumar. Lean Copilot: Large language models as copilots for theorem proving in Lean. In *PMLR* vol. 288 (NeuS), 2025.

[33] H. Lin, Z. Sun, Y. Yang, and S. Welleck. Lean-STaR: Learning to interleave thinking and proving. arXiv:2407.10040, 2024.

[34] Z. Li, J. Sun, L. Murphy, et al. A survey on deep learning for theorem proving. In *COLM*, 2024.

[35] L. de Moura and S. Ullrich. The Lean 4 theorem prover and programming language. In *CADE-28*, LNCS 12699, 625–635, 2021.

[36] The Coq Development Team. *The Coq Proof Assistant (Reference Manual)*. Zenodo, 2024. (Renamed The Rocq Prover, 2025.)

[37] T. Nipkow, L. C. Paulson, and M. Wenzel. *Isabelle/HOL: A Proof Assistant for Higher-Order Logic*. LNCS 2283, Springer, 2002.

[38] H.-J. Schurr, M. Fleury, H. Barbosa, and P. Fontaine. Alethe: Towards a generic SMT proof format. In *PxTP*, EPTCS, 2021.

[39] B. Andreotti, H. Lachnitt, and H. Barbosa. Carcara: An efficient proof checker and elaborator for SMT proofs in the Alethe format. In *TACAS*, LNCS 13993, 367–386, 2023.

[40] R. Nieuwenhuis, A. Oliveras, and C. Tinelli. Solving SAT and SAT modulo theories: From an abstract DPLL procedure to DPLL(T). *Journal of the ACM*, 53(6):937–977, 2006.

[41] N. Wetzler, M. J. H. Heule, and W. A. Hunt Jr. DRAT-trim: Efficient checking and trimming using expressive clausal proofs. In *SAT*, LNCS 8561, 422–429, 2014.

[42] D. Cousineau and G. Dowek. Embedding pure type systems in the $\lambda\Pi$-calculus modulo. In *TLCA*, LNCS 4583, 102–117, 2007.

[43] J. Lodder, B. Heeren, and J. Jeuring. Generating hints and feedback for Hilbert-style axiomatic proofs. In *ACM SIGCSE*, 387–392, 2017.

[44] J. Lodder, B. Heeren, J. Jeuring, and W. Neijenhuis. Generation and use of hints and feedback in a Hilbert-style axiomatic proof tutor. *International Journal of Artificial Intelligence in Education*, 31:99–133, 2021.

[45] B. Heeren, J. Jeuring, and A. Gerdes. Specifying rewrite strategies for interactive exercises. *Mathematics in Computer Science*, 3(3):349–370, 2010.

[46] M. Patel, et al. LeanTutor: A formally-verified AI tutor for mathematical proofs. arXiv:2506.08321, 2025.

[47] S. D. Tithi, A. K. Ramesh, C. DiMarco, et al. The promise and limits of LLMs in constructing proofs and hints for logic problems in intelligent tutoring systems. *Computers and Education: Artificial Intelligence*, 2025. arXiv:2505.04736.

[48] A. Martelli and U. Montanari. An efficient unification algorithm. *ACM TOPLAS*, 4(2):258–282, 1982.

[49] R. Dyckhoff. Contraction-free sequent calculi for intuitionistic logic. *The Journal of Symbolic Logic*, 57(3):795–807, 1992. (Corrigendum: *JSL* 83(4):1680–1682, 2018.)
