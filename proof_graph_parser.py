"""Trich xuat proof-DAG hai tang tu file JSONL dang {problem, solution[], answer}.

Output: file .graph.jsonl, moi dong la mot record chua:
    V_F: cac node menh de   (hypothesis, derived theo step, goal)
    V_R: cac node luat       (hyperedge: premise_set -> conclusion)
    E  : canh co huong        (F -> R va R -> F)

Suy luan canh giua cac step duoc lay tu ba nguon, theo do uu tien:
    1. Tham chieu tuong minh "Step k" / "from step k".
    2. Khop gia tri: ket qua (RHS, boxed, expression) cua step_i xuat hien o step_j.
    3. Fallback tuan tu: neu khong tim duoc tien de nao, tro ve step lien truoc
       (hoac F0 = hypothesis khi i = 1).
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Set, Tuple

# ---------------------------------------------------------------------------
# Regex
# ---------------------------------------------------------------------------

STEP_PREFIX = re.compile(r"^\s*Step\s*(\d+)\s*[:.\-]\s*", re.IGNORECASE)
EXPLICIT_REF = re.compile(
    r"\b(?:from\s+step|in\s+step|by\s+step|steps?)\s+(\d+)", re.IGNORECASE
)
INLINE_MATH = re.compile(
    r"\\\((.+?)\\\)|\\\[(.+?)\\\]|\$\$(.+?)\$\$|\$([^$]+?)\$",
    re.DOTALL,
)
NUMBER = re.compile(r"(?<![A-Za-z_\\\d])(-?\d+(?:\.\d+)?)")
BOXED = re.compile(r"\\boxed\{([^{}]+)\}")
SIMPLE_VAR = re.compile(r"\b([a-zA-Z]\w*)\b")
# A "result value" should be at least two chars long when not a multi-digit num
TRIVIAL_TOKENS = {"0", "1", "-1", "2", "x", "y", "z", "n", "a", "b", "c", "k"}


# ---------------------------------------------------------------------------
# Token extraction
# ---------------------------------------------------------------------------

def _math_bodies(text: str) -> List[str]:
    bodies = []
    for m in INLINE_MATH.finditer(text):
        body = next((g for g in m.groups() if g is not None), None)
        if body:
            bodies.append(body)
    return bodies


def _normalize(token: str) -> str:
    token = token.strip()
    token = re.sub(r"[\.,;]+$", "", token)
    token = token.replace("\\$", "").replace("$", "")
    token = token.replace("\\,", "").replace("\\;", "")
    token = re.sub(r"\s+", "", token)
    return token


def extract_numbers(text: str) -> Set[str]:
    """All numeric literals appearing in the text."""
    return {m.group(1) for m in NUMBER.finditer(text)}


def extract_step_results(step_text: str) -> Set[str]:
    """Values that look like the *output* of this step.

    Heuristic: the RHS of the last '=' inside each math block, plus everything
    wrapped in \\boxed{...}, plus any numeric literal sitting on that RHS.
    """
    results: Set[str] = set()

    for m in BOXED.finditer(step_text):
        token = _normalize(m.group(1))
        if token:
            results.add(token)

    for body in _math_bodies(step_text):
        parts = re.split(r"(?<![<>!:])=(?!=)", body)
        if len(parts) >= 2:
            rhs = parts[-1]
            tok = _normalize(rhs)
            if tok:
                results.add(tok)
            for n in NUMBER.finditer(rhs):
                results.add(_normalize(n.group(1)))

    # Boxed often appears in narrative outside of explicit math wrappers too
    return {r for r in results if r}


def extract_step_inputs(step_text: str) -> Set[str]:
    """All numeric/expression tokens that appear in this step (candidates for
    a backward edge to whichever earlier step *produced* them)."""
    tokens: Set[str] = set()
    tokens |= {_normalize(n) for n in extract_numbers(step_text)}
    for body in _math_bodies(step_text):
        for n in NUMBER.finditer(body):
            tokens.add(_normalize(n.group(1)))
        for atom in re.split(r"[=+\-*/(),\\\s]+", body):
            atom = _normalize(atom)
            if len(atom) >= 2:
                tokens.add(atom)
    return {t for t in tokens if t}


# ---------------------------------------------------------------------------
# Core parser
# ---------------------------------------------------------------------------

def _strip_step_prefix(step_text: str) -> Tuple[int | None, str]:
    m = STEP_PREFIX.match(step_text)
    if m:
        return int(m.group(1)), step_text[m.end():].strip()
    return None, step_text.strip()


def _record_id(problem: str, solution: Sequence[str]) -> str:
    h = hashlib.sha256()
    h.update(problem.encode("utf-8"))
    for s in solution:
        h.update(b"\x1f")
        h.update(s.encode("utf-8"))
    return h.hexdigest()[:16]


def parse_proof_graph(problem: str, solution: Sequence[str], answer: str) -> Dict:
    """Build the two-level proof graph for a single (problem, solution, answer)."""

    V_F: List[Dict] = []
    V_R: List[Dict] = []
    E: List[List[str]] = []

    # ---- Hypothesis node ----------------------------------------------------
    V_F.append({"id": "F0", "kind": "hypothesis", "text": problem})

    step_to_F: Dict[int, str] = {0: "F0"}
    results_of: Dict[int, Set[str]] = {0: extract_numbers(problem)}

    # ---- Derived nodes ------------------------------------------------------
    for i, raw in enumerate(solution, start=1):
        step_num, body = _strip_step_prefix(raw)
        F_id = f"F{i}"
        V_F.append(
            {
                "id": F_id,
                "kind": "derived",
                "step": i,
                "raw_step_number": step_num,
                "text": raw,
            }
        )
        step_to_F[i] = F_id
        results_of[i] = extract_step_results(raw)

    n = len(solution)

    # ---- Rule nodes ---------------------------------------------------------
    for i, raw in enumerate(solution, start=1):
        F_id = step_to_F[i]
        premises: Set[str] = set()
        evidence: List[str] = []

        # (1) Explicit references "step k"
        for m in EXPLICIT_REF.finditer(raw):
            ref = int(m.group(1))
            if 1 <= ref < i and ref in step_to_F:
                premises.add(step_to_F[ref])
                evidence.append(f"explicit_ref:Step{ref}")

        # (2) Value match: result of step_j appears as a token in step_i
        my_tokens = extract_step_inputs(raw)
        hyp_tokens = results_of[0]
        for prev_i in range(i - 1, 0, -1):
            prev_results = results_of.get(prev_i, set())
            informative = {
                t for t in prev_results
                if t and t not in TRIVIAL_TOKENS and t not in hyp_tokens
            }
            hit = informative & my_tokens
            if hit:
                premises.add(step_to_F[prev_i])
                evidence.append(
                    f"value_match:Step{prev_i}:{','.join(sorted(hit)[:3])}"
                )

        # (3) Fallback sequential chain
        if not premises:
            prev = i - 1
            premises.add(step_to_F[prev])
            evidence.append(
                "sequential_default:hyp" if prev == 0 else f"sequential_default:Step{prev}"
            )

        R_id = f"R{i}"
        V_R.append(
            {
                "id": R_id,
                "premises": sorted(premises),
                "conclusion": F_id,
                "evidence": evidence,
            }
        )
        for p in sorted(premises):
            E.append([p, R_id])
        E.append([R_id, F_id])

    # ---- Goal node ----------------------------------------------------------
    goal_F = f"F{n + 1}"
    V_F.append({"id": goal_F, "kind": "goal", "text": f"Answer: {answer}", "answer": answer})

    goal_R = f"R{n + 1}"
    last_premise = step_to_F[n] if n >= 1 else "F0"
    V_R.append(
        {
            "id": goal_R,
            "premises": [last_premise],
            "conclusion": goal_F,
            "evidence": ["final_answer"],
        }
    )
    E.append([last_premise, goal_R])
    E.append([goal_R, goal_F])

    # ---- Stats --------------------------------------------------------------
    arities = [len(r["premises"]) for r in V_R]
    return {
        "V_F": V_F,
        "V_R": V_R,
        "E": E,
        "stats": {
            "num_F": len(V_F),
            "num_R": len(V_R),
            "num_E": len(E),
            "max_arity": max(arities) if arities else 0,
            "mean_arity": round(sum(arities) / len(arities), 3) if arities else 0.0,
            "is_dag": True,
        },
    }


# ---------------------------------------------------------------------------
# I/O
# ---------------------------------------------------------------------------

def process_record(record: Dict) -> Dict:
    problem = record.get("problem", "")
    solution = record.get("solution", []) or []
    answer = record.get("answer", "")
    graph = parse_proof_graph(problem, solution, answer)
    return {
        "id": _record_id(problem, solution),
        "problem": problem,
        "answer": answer,
        **graph,
    }


def iter_jsonl(path: Path) -> Iterable[Dict]:
    with path.open("r", encoding="utf-8") as fp:
        for line in fp:
            line = line.strip()
            if not line:
                continue
            yield json.loads(line)


def process_file(input_path: Path, output_path: Path, *, limit: int | None = None,
                 progress_every: int = 500) -> Dict:
    output_path.parent.mkdir(parents=True, exist_ok=True)
    n = 0
    total_F = 0
    total_R = 0
    max_arity_global = 0
    with output_path.open("w", encoding="utf-8") as fout:
        for rec in iter_jsonl(input_path):
            out = process_record(rec)
            fout.write(json.dumps(out, ensure_ascii=False) + "\n")
            n += 1
            total_F += out["stats"]["num_F"]
            total_R += out["stats"]["num_R"]
            max_arity_global = max(max_arity_global, out["stats"]["max_arity"])
            if progress_every and n % progress_every == 0:
                print(f"  ... {n} records", file=sys.stderr)
            if limit and n >= limit:
                break
    return {
        "file": str(input_path),
        "out": str(output_path),
        "records": n,
        "total_F": total_F,
        "total_R": total_R,
        "max_arity": max_arity_global,
    }


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main() -> None:
    parser = argparse.ArgumentParser(description="Build proof-DAG JSONL.")
    parser.add_argument("inputs", nargs="+", type=Path,
                        help="Input JSONL files (or directories).")
    parser.add_argument("-o", "--out-dir", type=Path, required=True,
                        help="Directory where .graph.jsonl files are written.")
    parser.add_argument("--limit", type=int, default=None,
                        help="Max records per input file.")
    parser.add_argument("--suffix", default=".graph.jsonl",
                        help="Output file suffix (replaces .jsonl).")
    args = parser.parse_args()

    files: List[Path] = []
    for p in args.inputs:
        if p.is_dir():
            files.extend(sorted(p.rglob("*.jsonl")))
        else:
            files.append(p)

    summary = []
    for fp in files:
        out_name = fp.stem + args.suffix
        out_path = args.out_dir / fp.parent.name / out_name
        print(f"-> {fp.name}", file=sys.stderr)
        info = process_file(fp, out_path, limit=args.limit)
        summary.append(info)
        print(f"   wrote {info['records']} records, max arity {info['max_arity']}",
              file=sys.stderr)

    print(json.dumps(summary, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
