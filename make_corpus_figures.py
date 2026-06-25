"""Render real corpus proofs as TCIH event-hypergraphs using the *upgraded*
(faithful) parser — English labels, hypothesis-rooted + value-dependency edges
and rule classification (consistent with §8.9). Writes figures/corpus_*.png.
"""
from __future__ import annotations

import json
import textwrap
from pathlib import Path
from typing import Dict, Tuple

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyArrowPatch, FancyBboxPatch
from matplotlib.lines import Line2D

from tcih.nl_parser import reparse_edges

HERE = Path(__file__).resolve().parent
OUT = HERE / "out"
FIG = HERE / "figures"
FIG.mkdir(exist_ok=True)

COL = {"hypothesis": "#7fbf7b", "derived": "#a6cee3", "goal": "#fb9a99", "rule": "#fdae61"}
ESTYLE = {  # by faithful evidence type
    "value":      dict(color="#1f78b4", linewidth=1.8, linestyle="-"),
    "explicit":   dict(color="#1f78b4", linewidth=1.8, linestyle="-"),
    "hypothesis": dict(color="#b0b0b0", linewidth=0.9, linestyle="--"),
    "answer":     dict(color="#555555", linewidth=1.3, linestyle="-"),
}
RULE_ABBR = {"Compute": "Comp", "Conclude": "Concl", "ApplyFact": "Apply",
             "Define": "Def", "Solve": "Solve", "Compare": "Cmp",
             "Convert": "Cvt", "Generic": "Gen"}


def wrap(t, w=24, n=3):
    t = t.replace("\n", " ")
    L = textwrap.wrap(t, width=w)
    if len(L) > n:
        L = L[:n]; L[-1] = L[-1][:w - 1] + "…"
    return "\n".join(L)


def render(rec: Dict, title: str, out_png: Path):
    V_F = rec["V_F"]
    edges = reparse_edges(rec)
    n = sum(1 for f in V_F if f["kind"] == "derived")
    fx: Dict[str, Tuple[float, float]] = {}
    for f in V_F:
        if f["kind"] == "hypothesis":
            fx[f["id"]] = (0.0, 1.0)
        elif f["kind"] == "goal":
            fx[f["id"]] = (n + 1.0, 1.0)
        else:
            fx[f["id"]] = (float(f["step"]), 1.0)

    fig_w = max(8.0, 1.7 * (n + 2))
    fig, ax = plt.subplots(figsize=(fig_w, 4.8))
    ax.set_xlim(-0.8, n + 1.8); ax.set_ylim(-1.0, 2.0); ax.axis("off")
    ax.set_title(title, fontsize=10.5, loc="left")

    for f in V_F:
        x, y = fx[f["id"]]
        if f["kind"] == "derived":
            top, body = f"F{f['step']}", wrap(f["text"].split(":", 1)[-1].strip(), 22, 3)
        elif f["kind"] == "hypothesis":
            top, body = "F0 (hypothesis)", wrap(f["text"], 22, 4)
        else:
            top, body = "Goal", wrap(str(f.get("answer", f["text"])), 18, 2)
        ax.add_patch(FancyBboxPatch((x - 0.46, y - 0.30), 0.92, 0.60,
                     boxstyle="round,pad=0.02", facecolor=COL[f["kind"]],
                     edgecolor="black", linewidth=0.8, zorder=3))
        ax.text(x, y + 0.20, top, ha="center", va="center", fontsize=8, fontweight="bold", zorder=4)
        ax.text(x, y - 0.05, body, ha="center", va="center", fontsize=6.3, zorder=4)

    for f in V_F:
        fid = f["id"]
        if fid not in edges:
            continue
        info = edges[fid]
        prem = info["premises"]
        conc_x = fx[fid][0]
        prem_xs = [fx[p][0] for p in prem if p in fx]
        rx = (max(prem_xs) + conc_x) / 2.0 if prem_xs else conc_x - 0.5
        ry = 0.0
        ev = info["evidence"]
        st = ESTYLE.get(ev, ESTYLE["hypothesis"])
        abbr = RULE_ABBR.get(info["rule"], info["rule"][:4])
        ax.add_patch(FancyBboxPatch((rx - 0.22, ry - 0.15), 0.44, 0.30,
                     boxstyle="round,pad=0.01", facecolor=COL["rule"],
                     edgecolor="black", linewidth=0.8, zorder=3))
        ax.text(rx, ry, f"{abbr}\n∧={len(prem)}", ha="center", va="center",
                fontsize=6.0, fontweight="bold", zorder=4)
        for p in prem:
            if p not in fx:
                continue
            px, py = fx[p]
            ax.add_patch(FancyArrowPatch((px, py - 0.30), (rx, ry + 0.15),
                         arrowstyle="-|>", mutation_scale=8,
                         connectionstyle="arc3,rad=0.12", zorder=2, **st))
        ax.add_patch(FancyArrowPatch((rx, ry + 0.15), (conc_x, fx[fid][1] - 0.30),
                     arrowstyle="-|>", mutation_scale=8,
                     connectionstyle="arc3,rad=-0.12", zorder=2, **st))

    legend = [
        Line2D([0], [0], marker="s", color="w", label="hypothesis", markerfacecolor=COL["hypothesis"], markeredgecolor="k", markersize=10),
        Line2D([0], [0], marker="s", color="w", label="derived step", markerfacecolor=COL["derived"], markeredgecolor="k", markersize=10),
        Line2D([0], [0], marker="s", color="w", label="goal", markerfacecolor=COL["goal"], markeredgecolor="k", markersize=10),
        Line2D([0], [0], marker="s", color="w", label="rule event (∧, classified)", markerfacecolor=COL["rule"], markeredgecolor="k", markersize=10),
        Line2D([0], [0], color="#1f78b4", lw=1.8, label="value dependency"),
        Line2D([0], [0], color="#b0b0b0", lw=0.9, ls="--", label="hypothesis-attached"),
        Line2D([0], [0], color="#555555", lw=1.3, label="goal edge"),
    ]
    ax.legend(handles=legend, loc="lower center", bbox_to_anchor=(0.5, -0.16),
              ncol=4, fontsize=7, frameon=False)
    fig.tight_layout()
    fig.savefig(out_png, dpi=160, bbox_inches="tight")
    plt.close(fig)


def pick(path: Path, idx: int) -> Dict:
    with path.open(encoding="utf-8") as fp:
        for i, line in enumerate(fp):
            if i == idx:
                return json.loads(line)
    raise IndexError(idx)


EXAMPLES = [
    ("data_1/number_theory_arithmetic_1.graph.jsonl", 0,
     "Arithmetic — multi-source aggregation (the total step depends on the item steps)"),
    ("data_1/algebra_1.graph.jsonl", 0,
     "Algebra — a short computational chain"),
    ("data_1/calculus_analysis_1.graph.jsonl", 484,
     "Calculus/analysis — a deeper proof with value dependencies"),
    ("data_4/logic_foundations.graph.jsonl", 0,
     "Propositional logic — parallel steps rooted at the hypothesis"),
]


def main():
    for rel, idx, label in EXAMPLES:
        p = OUT / rel
        if not p.exists():
            print("missing", p); continue
        rec = pick(p, idx)
        slug = "corpus_" + rel.split("/")[-1].replace(".graph.jsonl", "")
        prob = rec["problem"][:88].replace("\n", " ")
        render(rec, f"{label}\nproblem: {prob}{'…' if len(rec['problem'])>88 else ''}",
               FIG / f"{slug}.png")
        print("wrote", FIG / f"{slug}.png")


if __name__ == "__main__":
    main()
