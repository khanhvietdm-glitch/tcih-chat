"""Render proof-DAG records as bipartite (F/R) layered images."""

from __future__ import annotations

import json
import textwrap
from pathlib import Path
from typing import Dict, Tuple

import matplotlib.pyplot as plt
from matplotlib.patches import FancyArrowPatch, Rectangle
from matplotlib.lines import Line2D

OUT = Path(r"C:\Users\pc\OneDrive\Documents\proof_graph\out")
IMG = Path(r"C:\Users\pc\OneDrive\Documents\proof_graph\figures")
IMG.mkdir(exist_ok=True)


def evidence_kind(ev_list) -> str:
    if any(e.startswith("explicit_ref") for e in ev_list):
        return "explicit"
    if any(e.startswith("value_match") for e in ev_list):
        return "value"
    if any(e.startswith("final_answer") for e in ev_list):
        return "final"
    return "seq"


COLORS = {
    "hypothesis": "#7fbf7b",
    "derived":    "#a6cee3",
    "goal":       "#fb9a99",
    "rule":       "#fdae61",
}
EDGE_STYLE = {
    "explicit": dict(color="#1f78b4", linewidth=1.6, linestyle="-"),
    "value":    dict(color="#1f78b4", linewidth=1.6, linestyle="-"),
    "final":    dict(color="#666666", linewidth=1.2, linestyle="-"),
    "seq":      dict(color="#bbbbbb", linewidth=1.0, linestyle="--"),
}


def wrap(text: str, width: int = 28, max_lines: int = 4) -> str:
    text = text.replace("\n", " ")
    lines = textwrap.wrap(text, width=width)
    if len(lines) > max_lines:
        lines = lines[:max_lines]
        lines[-1] = lines[-1][: max(0, width - 1)] + "…"
    return "\n".join(lines)


def render(record: Dict, title: str, out_png: Path) -> None:
    V_F = record["V_F"]
    V_R = record["V_R"]
    n_steps = sum(1 for f in V_F if f["kind"] == "derived")

    # Positions
    F_pos: Dict[str, Tuple[float, float]] = {}
    R_pos: Dict[str, Tuple[float, float]] = {}
    for f in V_F:
        if f["kind"] == "hypothesis":
            F_pos[f["id"]] = (0.0, 1.0)
        elif f["kind"] == "goal":
            F_pos[f["id"]] = (n_steps + 1.0, 1.0)
        else:
            F_pos[f["id"]] = (float(f["step"]), 1.0)
    # R node sits between its premises' max x and its conclusion
    for r in V_R:
        conc_x = F_pos[r["conclusion"]][0]
        prem_xs = [F_pos[p][0] for p in r["premises"]]
        x = (max(prem_xs) + conc_x) / 2.0 if prem_xs else conc_x - 0.5
        R_pos[r["id"]] = (x, 0.0)

    # Figure size scales with steps
    fig_w = max(8.0, 1.6 * (n_steps + 2))
    fig_h = 4.6
    fig, ax = plt.subplots(figsize=(fig_w, fig_h))
    ax.set_xlim(-0.7, n_steps + 1.7)
    ax.set_ylim(-0.9, 1.9)
    ax.axis("off")
    ax.set_title(title, fontsize=11, loc="left")

    # ---- Draw F nodes (proposition) ----------------------------------------
    for f in V_F:
        x, y = F_pos[f["id"]]
        color = COLORS[f["kind"]]
        if f["kind"] == "derived":
            label_top = f"F{f['step']}"
            body = wrap(f["text"].split(":", 1)[-1].strip() if ":" in f["text"] else f["text"], 24, 3)
        elif f["kind"] == "hypothesis":
            label_top = "F0 (giả thiết)"
            body = wrap(f["text"], 24, 4)
        else:
            label_top = "Goal"
            body = wrap(f.get("answer", f["text"]), 24, 2)
        ax.add_patch(Rectangle((x - 0.45, y - 0.28), 0.9, 0.56,
                               facecolor=color, edgecolor="black", linewidth=0.8,
                               zorder=3))
        ax.text(x, y + 0.18, label_top, ha="center", va="center",
                fontsize=8, fontweight="bold", zorder=4)
        ax.text(x, y - 0.06, body, ha="center", va="center", fontsize=6.5, zorder=4)

    # ---- Draw R nodes (rule = hyperedge) -----------------------------------
    ev_kind_map = {}
    for r in V_R:
        kind = evidence_kind(r["evidence"])
        ev_kind_map[r["id"]] = kind
        x, y = R_pos[r["id"]]
        arity = len(r["premises"])
        label = f"R{r['id'][1:]}\n∧={arity}"
        ax.add_patch(Rectangle((x - 0.18, y - 0.14), 0.36, 0.28,
                               facecolor=COLORS["rule"], edgecolor="black",
                               linewidth=0.8, zorder=3))
        ax.text(x, y, label, ha="center", va="center", fontsize=6.5,
                fontweight="bold", zorder=4)

    # ---- Draw edges --------------------------------------------------------
    for r in V_R:
        kind = ev_kind_map[r["id"]]
        style = EDGE_STYLE[kind]
        rx, ry = R_pos[r["id"]]
        for p in r["premises"]:
            px, py = F_pos[p]
            arrow = FancyArrowPatch(
                (px, py - 0.28), (rx, ry + 0.14),
                arrowstyle="-|>", mutation_scale=8,
                connectionstyle="arc3,rad=0.12",
                zorder=2, **style,
            )
            ax.add_patch(arrow)
        cx, cy = F_pos[r["conclusion"]]
        arrow = FancyArrowPatch(
            (rx, ry + 0.14), (cx, cy - 0.28),
            arrowstyle="-|>", mutation_scale=8,
            connectionstyle="arc3,rad=-0.12",
            zorder=2, **style,
        )
        ax.add_patch(arrow)

    # ---- Legend ------------------------------------------------------------
    legend_items = [
        Line2D([0], [0], marker="s", color="w", label="Hypothesis",
               markerfacecolor=COLORS["hypothesis"], markeredgecolor="k", markersize=10),
        Line2D([0], [0], marker="s", color="w", label="Derived step (F)",
               markerfacecolor=COLORS["derived"], markeredgecolor="k", markersize=10),
        Line2D([0], [0], marker="s", color="w", label="Goal",
               markerfacecolor=COLORS["goal"], markeredgecolor="k", markersize=10),
        Line2D([0], [0], marker="s", color="w", label="Rule R (siêu cạnh AND)",
               markerfacecolor=COLORS["rule"], markeredgecolor="k", markersize=10),
        Line2D([0], [0], color="#1f78b4", lw=1.6, label="value_match / explicit_ref"),
        Line2D([0], [0], color="#bbbbbb", lw=1.0, ls="--", label="sequential_default"),
        Line2D([0], [0], color="#666666", lw=1.2, label="final_answer"),
    ]
    ax.legend(handles=legend_items, loc="lower center",
              bbox_to_anchor=(0.5, -0.18), ncol=4, fontsize=7, frameon=False)
    plt.tight_layout()
    plt.savefig(out_png, dpi=160, bbox_inches="tight")
    plt.close(fig)


def pick(path: Path, index: int) -> Dict:
    with path.open(encoding="utf-8") as fp:
        for i, line in enumerate(fp):
            if i == index:
                return json.loads(line)
    raise IndexError(index)


def main() -> None:
    examples = [
        ("data_1/algebra_1.graph.jsonl", 0,
         "Đại số (Mrs. Carlton — chuỗi tính điểm phạt)"),
        ("data_1/number_theory_arithmetic_1.graph.jsonl", 0,
         "Số học (Judy đi siêu thị — siêu cạnh AND ở R6)"),
        ("data_1/calculus_analysis_1.graph.jsonl", 484,
         "Giải tích (chứng minh phức tạp — mean_arity≈2.4)"),
        ("data_4/logic_foundations.graph.jsonl", 0,
         "Logic mệnh đề (chuỗi suy luận thuần — tất cả arity=1)"),
    ]
    for rel, idx, label in examples:
        rec = pick(OUT / rel, idx)
        slug = rel.split("/")[-1].replace(".graph.jsonl", "") + f"__idx{idx}"
        out = IMG / f"{slug}.png"
        title = f"{label}\nproblem: {rec['problem'][:90].replace(chr(10),' ')}{'…' if len(rec['problem'])>90 else ''}"
        render(rec, title, out)
        print(f"wrote {out}  ({rec['stats']})")


if __name__ == "__main__":
    main()
