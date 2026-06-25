"""Regression suite for the corrected TCIH core.

Each test pins down one of the corrections demanded by the editorial review, so
the suite doubles as machine-checked evidence that the redesign is coherent.
Run with:  PYTHONUTF8=1 python -m pytest -q
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from tcih.formula import And, Atom, Imp, Not, parse, apply_subst, match
from tcih.check import structural_check
from tcih.oracle import valid, entails, all_edges_sound
from tcih.prover import ipc_provable, prove
from tcih.gallery import GALLERY, a_imp_a, bad_fold_base
from tcih.fold import (content_only_fold, context_preserving_fold,
                       antichain_counterexample, rank_certifies_acyclic,
                       repeated_lemma, vertex_rank)
from tcih.granularity import length_law
from tcih.search import (forward_chain, admissibility_counterexample,
                         astar_admissibility_demo)
from tcih.diagnose import diagnose, inject
from tcih.nl_parser import reparse_edges, to_tcih, dependency_gaps
from tcih.smt_oracle import verify_step


# ---- formula layer --------------------------------------------------------
def test_parse_and_print():
    assert str(parse("A -> (B -> A)")) == "A ⇒ B ⇒ A"
    assert str(parse("~(A&B)|C")) == "¬(A ∧ B) ∨ C"

def test_match_apply():
    s = match(Imp(Atom("A"), Atom("B")), parse("(P|Q)->R"))
    assert s is not None and str(apply_subst(Imp(Atom("A"), Atom("B")), s)) == "P ∨ Q ⇒ R"


# ---- model & checker ------------------------------------------------------
def test_gallery_all_wellformed():
    for name, fn in GALLERY.items():
        assert structural_check(fn()).ok, name

def test_a_imp_a_representable():       # review 4.5
    g = a_imp_a()
    assert structural_check(g).ok and len(g.events) == 2


# ---- folding (review 4.4, 4.7, 4.8) ---------------------------------------
def test_content_only_fold_unsound():
    g, _ = bad_fold_base()
    assert not structural_check(content_only_fold(g)).ok

def test_context_preserving_fold_sound():
    g, _ = bad_fold_base()
    assert structural_check(context_preserving_fold(g)).ok

def test_repeated_lemma_shared_soundly():
    g = repeated_lemma()
    f = context_preserving_fold(g)
    assert structural_check(f).ok and len(f.vertices) < len(g.vertices)

def test_antichain_counterexample():    # review 4.7
    ce = antichain_counterexample()
    assert ce["each_class_is_antichain"] and ce["quotient_has_cycle"]


# ---- granularity (review 4.9) ---------------------------------------------
def test_granularity_length_law():
    for k in (1, 2, 3, 5):
        r = length_law(k)
        assert r["law_holds"] and r["roundtrip_edges_match"]
        assert r["outside_blocks_preserved"]
        assert r["coarse_wellformed"] and r["expanded_wellformed"]


# ---- decision procedure & the De Morgan correction (review 4.13) ----------
def test_ipc_vs_classical():
    assert ipc_provable([], parse("~(A|B) -> (~A & ~B)"))
    assert ipc_provable([], parse("(~A & ~B) -> ~(A|B)"))
    assert not ipc_provable([], parse("~(A&B) -> (~A | ~B)"))   # the bogus one
    assert valid(parse("~(A&B) -> (~A | ~B)"))                  # but classically valid

def test_prove_constructs_verified_proofs():
    cases = [("A->A", [], False), ("(A->B)->((B->C)->(A->C))", [], False),
             ("Q", ["P", "P->Q"], False), ("~A & ~B", ["~(A|B)"], False),
             ("A | ~A", [], True), ("((A->B)->A)->A", [], True)]
    for goal, asm, classical in cases:
        g = prove(parse(goal), [parse(a) for a in asm], classical=classical)
        assert g is not None, goal
        assert structural_check(g).ok and not all_edges_sound(g), goal


# ---- search (review 4.12, 4.11/4.6 Horn) ----------------------------------
def test_astar_admissibility_fix():
    c = admissibility_counterexample()
    assert c["still_inadmissible"]                       # min(h,b)=8 > h*=5
    d = astar_admissibility_demo()
    assert d["admissible_returns_optimal"]
    assert d["inadmissible_suboptimal"]

def test_forward_chain_horn():
    res = forward_chain({"a"}, [(("a",), "b"), (("b",), "c"), (("c", "a"), "d")])
    assert res["closure"] == {"a", "b", "c", "d"}


# ---- diagnosis ------------------------------------------------------------
def test_inject_detect():
    base = GALLERY["hypothetical_syllogism"]()
    assert diagnose(base)["ok"]
    for kind in ("E1", "E2", "E3", "E4"):
        g2, label = inject(base, kind)
        d = diagnose(g2)
        assert label["class"] in d["classes"], kind
        assert d["locus_event"] is not None


# ---- corpus parser (D4 -> D5) ---------------------------------------------
def test_corpus_parser_faithful_structure():
    rec = {
        "problem": "Compute the total cost of apples and milk.",
        "answer": "21",
        "V_F": [
            {"id": "F0", "kind": "hypothesis", "text": "Compute the total cost of apples and milk."},
            {"id": "F1", "kind": "derived", "text": "Step 1: apples cost \\(4 \\cdot 3 = 12\\)."},
            {"id": "F2", "kind": "derived", "text": "Step 2: milk costs \\(3 \\cdot 3 = 9\\)."},
            {"id": "F3", "kind": "derived", "text": "Step 3: total \\(12 + 9 = 21\\)."},
            {"id": "F4", "kind": "goal", "text": "Answer: 21"},
        ],
        "V_R": [], "E": [],
    }
    edges = reparse_edges(rec)
    # parallel steps root at the hypothesis, not chained to the previous step
    assert edges["F1"]["premises"] == ["F0"]
    assert edges["F2"]["premises"] == ["F0"]
    # the aggregation step is genuinely multi-source (uses 12 and 9)
    assert set(edges["F3"]["premises"]) == {"F1", "F2"}
    # the reconstructed TCIH passes the corrected checker; no missing deps
    assert structural_check(to_tcih(rec, edges)).ok
    assert dependency_gaps(rec, edges) == []
    # dropping a real dependency is detected
    edges["F3"]["premises"] = ["F1"]
    assert "F3" in dependency_gaps(rec, edges)


# ---- SMT/CAS semantic oracle ----------------------------------------------
def test_smt_oracle():
    assert verify_step(r"\(5 \cdot 1 = 5\)") == "valid"
    assert verify_step(r"\(443 + 73 + 358 = 874\)") == "valid"
    assert verify_step(r"\(\frac{8+4}{2} = 6\)") == "valid"          # nested ok
    assert verify_step(r"\(\frac{1}{-\sqrt{2}} = -\frac{\sqrt{2}}{2}\)") == "valid"
    assert verify_step(r"\(2 + 2 = 5\)") == "invalid"                # genuine E4
    assert verify_step(r"\(\sqrt{16} = 5\)") == "invalid"
    assert verify_step(r"\(x = 4\)") == "symbolic"                   # deferred
    assert verify_step(r"\(5000/7 = 714.29\)") == "rounding"         # = used for ≈
    assert verify_step("no math here") == "no_claim"
    # ambiguous percent and transcendental claims are deferred, not guessed
    assert verify_step(r"\(20\% \cdot 30 = 6\)") == "no_claim"
    assert verify_step(r"\(4\log_2 2 = 4\)") == "no_claim"


def test_contextual_smt():
    import sympy
    from sympy.abc import x, y
    from tcih.smt_oracle import entails_smt
    A = [(x, sympy.Integer(4), "="), (y, sympy.Integer(-20), "=")]
    assert entails_smt(A, x + y, sympy.Integer(-16), "=") == "valid"
    assert entails_smt(A, x + y, sympy.Integer(-15), "=") == "invalid"
    assert entails_smt(A, x, y, ">") == "valid"                      # 4 > -20
    # nonlinear / sqrt under an assumption
    s = sympy.sqrt(6) - sympy.sqrt(2)
    assert entails_smt([(x, s, "=")], x + 2, sympy.Integer(0), ">") == "valid"
    # genuinely under-determined without enough assumptions
    assert entails_smt([], x, sympy.Integer(5), "=") == "underdetermined"


def test_lean_backend_if_available():
    from tcih.lean_backend import lean_available, check_arith
    if not lean_available():
        pytest.skip("no Lean toolchain on this machine")
    import sympy
    assert check_arith(sympy.Integer(2) + 2, sympy.Integer(4), "=") == "valid"
    assert check_arith(sympy.Integer(2) + 2, sympy.Integer(5), "=") == "invalid"


def test_mathlib_nonlinear_if_enabled():
    import os
    if not os.environ.get("TCIH_TEST_MATHLIB"):
        pytest.skip("set TCIH_TEST_MATHLIB=1 to run the slow Lean+mathlib check")
    from tcih.lean_backend import mathlib_available, check_nonlinear
    if not mathlib_available():
        pytest.skip("mathlib project not built")
    assert check_nonlinear(
        "example (x y : ℝ) : x^2 + y^2 ≥ 2*x*y := by nlinarith [sq_nonneg (x - y)]") == "proved"
    assert check_nonlinear("example (x : ℝ) : x^2 ≥ 1 := by nlinarith") == "unproved"
