"""Generate the paper's figures from the measured artefacts:
  figures/fig_scaling.png   — StructuralCheck O(N) scaling (from results.json)
  figures/fig_coverage.png  — semantic-oracle coverage + the 4-tier stack
                              (from context2_eval / semantic_eval / lean_eval)
All numbers are read from artifacts/, never hard-coded.
"""
from __future__ import annotations

import json
from pathlib import Path

import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch, FancyArrowPatch

HERE = Path(__file__).resolve().parent
ART = HERE / "artifacts"
FIG = HERE / "figures"
FIG.mkdir(exist_ok=True)

plt.rcParams.update({"font.size": 10, "font.family": "DejaVu Sans",
                     "axes.grid": True, "grid.alpha": 0.3, "figure.dpi": 200})
BLUE, GREEN, ORANGE, GRAY = "#2E6FB7", "#3a9a52", "#e08a1e", "#9aa0a6"


def fig_scaling():
    data = json.loads((ART / "results.json").read_text(encoding="utf-8"))["scaling"]
    N = np.array([r["N"] for r in data], float)
    us = np.array([r["us_per_check"] for r in data], float)
    upn = np.array([r["us_per_N"] for r in data], float)

    fig, (axL, axR) = plt.subplots(1, 2, figsize=(9.2, 3.6))
    # left: log-log time vs N with power-law fit
    axL.loglog(N, us, "o", color=BLUE, ms=6, label="measured")
    a, b = np.polyfit(np.log(N), np.log(us), 1)
    xs = np.array([N.min(), N.max()])
    axL.loglog(xs, np.exp(b) * xs ** a, "-", color=BLUE, lw=1.5,
               label=f"fit: slope = {a:.2f}")
    axL.loglog(xs, us[0] * xs / N[0], "--", color=GRAY, lw=1.2, label="slope 1 (linear)")
    axL.set_xlabel("encoded input size  N")
    axL.set_ylabel("StructuralCheck time  (µs)")
    axL.set_title("(a) Checking time vs N (log–log)")
    axL.legend(frameon=False, fontsize=8)
    # right: per-node cost flat
    axR.semilogx(N, upn, "s-", color=GREEN, ms=6)
    axR.set_ylim(0, max(upn) * 1.6)
    axR.set_xlabel("encoded input size  N")
    axR.set_ylabel("per-node cost  (µs / N)")
    axR.set_title("(b) Per-node cost is flat  ⇒  O(N)")
    axR.axhline(upn.mean(), color=ORANGE, ls="--", lw=1.2,
                label=f"mean = {upn.mean():.2f} µs/N")
    axR.legend(frameon=False, fontsize=8)
    fig.tight_layout()
    fig.savefig(FIG / "fig_scaling.png", bbox_inches="tight")
    plt.close(fig)


def fig_coverage():
    ctx = json.loads((ART / "context2_eval.json").read_text(encoding="utf-8"))
    sem = json.loads((ART / "semantic_eval.json").read_text(encoding="utf-8"))
    lean = json.loads((ART / "lean_eval.json").read_text(encoding="utf-8"))
    noclaim = ctx["full_status_pct"]["no_claim"]
    stages = ["Z3 ground\n(§8.10)", "+ premise\ncontext", "+ problem\nprose"]
    dec = [ctx["baseline_decidable_pct"], ctx["premise_context_decidable_pct"],
           ctx["full_context_decidable_pct"]]
    sym = [100 - noclaim - d for d in dec]
    ncl = [noclaim] * 3

    fig, (axL, axR) = plt.subplots(1, 2, figsize=(9.6, 3.7),
                                   gridspec_kw={"width_ratios": [1.05, 1.0]})
    y = np.arange(3)
    axL.barh(y, dec, color=GREEN, label="decidable (valid/invalid/rounding)")
    axL.barh(y, sym, left=dec, color=ORANGE, label="symbolic (deferred)")
    axL.barh(y, ncl, left=[d + s for d, s in zip(dec, sym)], color=GRAY,
             label="no formal claim")
    for yi, d in zip(y, dec):
        axL.text(d / 2, yi, f"{d:.1f}%", va="center", ha="center",
                 color="white", fontsize=9, fontweight="bold")
    axL.set_yticks(y); axL.set_yticklabels(stages)
    axL.set_xlabel("share of steps  (%)"); axL.set_xlim(0, 100)
    axL.invert_yaxis()
    axL.set_title("(a) Semantic coverage grows with context")
    axL.legend(frameon=False, fontsize=7.5, loc="lower right")
    axL.grid(axis="y")

    # right: the 4-tier oracle stack
    axR.set_xlim(0, 1); axR.set_ylim(0, 1); axR.axis("off")
    axR.set_title("(b) The four-tier semantic oracle stack")
    tiers = [
        ("4  Lean + mathlib  (nlinarith / norm_num)", "nonlinear & √ inequalities proved", "#6a4ea3"),
        ("3  Lean 4 kernel  (by decide)", f"{lean['lean_z3_agreement']*100:.0f}% agreement with Z3", "#2E6FB7"),
        (f"2  Z3 contextual  (assumptions, √)", f"coverage {dec[2]:.1f}%", GREEN),
        (f"1  Z3 ground arithmetic", f"E4 recall {sem['e4_injection']['recall']}", ORANGE),
    ]
    h = 0.21
    for i, (title, sub, col) in enumerate(tiers):
        yb = 0.04 + i * (h + 0.03)
        box = FancyBboxPatch((0.03, yb), 0.94, h, boxstyle="round,pad=0.01",
                             linewidth=1.2, edgecolor=col, facecolor=col + "22")
        axR.add_patch(box)
        axR.text(0.06, yb + h * 0.62, title, fontsize=9, fontweight="bold", color=col)
        axR.text(0.06, yb + h * 0.22, sub, fontsize=8, color="#333333")
    axR.annotate("faster", xy=(0.0, 0.05), xytext=(0.0, 0.95), fontsize=8,
                 color=GRAY, ha="center",
                 arrowprops=dict(arrowstyle="->", color=GRAY))
    axR.text(-0.02, 0.5, "higher assurance →", rotation=90, va="center",
             ha="center", fontsize=8, color=GRAY)
    fig.tight_layout()
    fig.savefig(FIG / "fig_coverage.png", bbox_inches="tight")
    plt.close(fig)


def fig_pipeline():
    """TCIH-Chat architecture: the S1–S5 pipeline with the verify-and-repair loop
    and the four-tier oracle, over the shared TCIH event-hypergraph."""
    fig, ax = plt.subplots(figsize=(10.2, 4.8))
    ax.set_xlim(0, 116); ax.set_ylim(0, 100); ax.axis("off")

    def box(x, y, w, h, title, sub, col, tcol=None, fs=9):
        ax.add_patch(FancyBboxPatch((x, y), w, h, boxstyle="round,pad=0.4",
                     linewidth=1.3, edgecolor=col, facecolor=col + "1f"))
        ax.text(x + w / 2, y + h - 4.2, title, ha="center", va="top",
                fontsize=fs, fontweight="bold", color=tcol or col)
        if sub:
            ax.text(x + w / 2, y + 4.0, sub, ha="center", va="bottom",
                    fontsize=7.2, color="#333333")

    def arrow(x1, y1, x2, y2, col="#444444", rad=0.0, lw=1.6, ls="-"):
        ax.add_patch(FancyArrowPatch((x1, y1), (x2, y2), arrowstyle="-|>",
                     mutation_scale=14, lw=lw, color=col, linestyle=ls,
                     connectionstyle=f"arc3,rad={rad}", zorder=5))

    # input
    box(2, 80, 22, 14, "Input (user / LLM)", "goal · candidate proof · prose", "#6a4ea3")
    # five stages
    sx, sw, sy, sh, gap = 3, 16.5, 46, 20, 2.0
    stages = [
        ("S1 · Intake", "parse to TCIH\n(goal / proof / steps)", BLUE),
        ("S2 · Construct", "G4ip · ND synth\n· nl_parser", GREEN),
        ("S3 · Verify", "StructuralCheck O(N)\n+ oracle  (trusted base)", ORANGE),
        ("S4 · Diagnose", "E1–E6 · localize\nminimal subproof", "#c0504d"),
        ("S5 · Explain", "numbered ND steps\n· granularity", "#2E6FB7"),
    ]
    xs = []
    for i, (t, s, c) in enumerate(stages):
        x = sx + i * (sw + gap)
        xs.append(x)
        box(x, sy, sw, sh, t, s, c, fs=9)
        if i > 0:
            arrow(xs[i - 1] + sw, sy + sh / 2, x, sy + sh / 2)
    # input -> S1
    arrow(13, 80, 13, sy + sh)
    # output to the right of S5
    arrow(xs[-1] + sw, sy + sh / 2, xs[-1] + sw + 3.5, sy + sh / 2, col="#2E6FB7")
    ax.text(xs[-1] + sw + 4.5, sy + sh / 2, "verified proof /\nlocalized\ndiagnosis",
            ha="left", va="center", fontsize=8.5, fontweight="bold", color="#2E6FB7")
    # verify-and-repair feedback loop  S4 -> Input
    arrow(xs[3] + sw / 2, sy + sh, 21, 80, col="#c0504d", rad=0.32, ls="--")
    ax.text(48, 90, "verify-and-repair loop:\nlocalized, class-tagged feedback",
            ha="center", va="center", fontsize=7.6, color="#c0504d")
    # shared TCIH substrate band
    ax.add_patch(FancyBboxPatch((sx, 30), 5 * (sw + gap) - gap, 10,
                 boxstyle="round,pad=0.3", linewidth=1.2, edgecolor="#555",
                 facecolor="#5551", linestyle="--"))
    ax.text(sx + (5 * (sw + gap) - gap) / 2, 35,
            "shared substrate:  TCIH ordered event-hypergraph   v = (id, Γ ⊢ φ, τ)   "
            "e = (S, t, R[σ], D, prov)", ha="center", va="center",
            fontsize=8, style="italic", color="#333")
    # oracle stack mini-note under S3
    ax.text(xs[2] + sw / 2, 27,
            "oracle: Z3 ground → Z3 ctx → Lean → mathlib", ha="center",
            fontsize=6.6, color=ORANGE)
    ax.set_title("TCIH-Chat pipeline architecture", fontsize=12, fontweight="bold")
    fig.savefig(FIG / "fig_pipeline.png", bbox_inches="tight")
    plt.close(fig)


if __name__ == "__main__":
    fig_scaling()
    fig_coverage()
    fig_pipeline()
    for n in ("fig_scaling", "fig_coverage", "fig_pipeline"):
        print("wrote", FIG / f"{n}.png")
