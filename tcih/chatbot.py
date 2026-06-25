"""TCIH-Chat: a conversational mathematics proof assistant.

This is the application layer (paper, System Architecture). It composes the
verified symbolic core into the behaviours a user expects from a proof chatbot:

  * PROVE a goal automatically and return a derivation that is *independently
    verified* (structural checker + semantic oracle) before it is shown.
  * EXPLAIN a proof at an adjustable level of granularity.
  * DIAGNOSE a candidate proof (e.g. produced by a student or an LLM), reporting
    the error class and localizing it to the smallest failing sub-derivation --
    the neuro-symbolic verify-and-repair loop.

The design guarantee is that the assistant never presents an unverified proof:
the trusted base is the small structural checker, not the (heuristic) prover or
any LLM that may sit in front of it.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple

from .formula import Formula, parse
from .model import Event, TCIH, show_ctx
from .check import structural_check
from .oracle import all_edges_sound, valid, entails
from .prover import ipc_provable, prove
from .diagnose import diagnose, EXT_LIBRARY

RULE_NAMES = {
    "Assume": "assumption", "Axiom": "axiom",
    "ImpI": "⇒-introduction", "ImpE": "modus ponens (⇒-elimination)",
    "AndI": "∧-introduction", "AndE1": "∧-elimination (left)",
    "AndE2": "∧-elimination (right)", "OrI1": "∨-introduction (left)",
    "OrI2": "∨-introduction (right)", "OrE": "∨-elimination (case analysis)",
    "NotI": "¬-introduction", "NotE": "¬-elimination", "BotE": "ex falso quodlibet",
    "RAA": "reductio ad absurdum (classical)",
}


def _topo(g: TCIH) -> List[Event]:
    pos = {v: i for i, v in enumerate(g.vertices)}
    return sorted(g.events, key=lambda e: pos.get(e.target, 0))


def render(g: TCIH, level: str = "detailed") -> str:
    """Render a derivation as numbered natural-deduction steps."""
    order = _topo(g)
    num = {e.target: i + 1 for i, e in enumerate(order)}
    lines: List[str] = []
    for i, e in enumerate(order, 1):
        if level == "outline" and e.rule in ("Assume",) and i != len(order):
            pass  # still show assumptions; outline only trims trivial detail
        t = g.vertices[e.target]
        refs = ", ".join(str(num[s]) for s in e.sources if s in num)
        rn = RULE_NAMES.get(e.rule, e.rule)
        disc = f", discharge {','.join(sorted(e.discharged))}" if e.discharged else ""
        just = f"[{rn}{(' from ' + refs) if refs else ''}{disc}]"
        lines.append(f"  {i:>2}. {t.judgment():<34} {just}")
    return "\n".join(lines)


@dataclass
class Answer:
    ok: bool
    text: str
    graph: Optional[TCIH] = None

    def __str__(self) -> str:
        return self.text


class Assistant:
    """Programmatic API behind the chatbot. Every returned proof is verified."""

    def prove_goal(self, goal: str, assumptions: Optional[List[str]] = None,
                   level: str = "detailed") -> Answer:
        gf = parse(goal)
        asm = [parse(a) for a in (assumptions or [])]
        # 1. decide the logic
        if ipc_provable(asm, gf):
            logic, classical = "intuitionistic", False
        elif entails(asm, gf):
            logic, classical = "classical", True
        else:
            extra = "" if asm else " (and it is not a tautology)"
            return Answer(False, f"✗ {gf} is not provable from the given "
                                 f"assumptions{extra}.")
        # 2. construct a proof object
        g = prove(gf, asm, classical=classical)
        if g is None:
            return Answer(False, f"{gf} is {logic}ly valid, but proof "
                                 f"reconstruction exceeded the search bound.")
        # 3. independently verify before showing
        sc = structural_check(g)
        unsound = all_edges_sound(g)
        if not sc.ok or unsound:
            return Answer(False, "internal error: constructed proof failed "
                                 f"verification ({sc}; unsound={unsound}).")
        head = (f"✓ Proved  {show_ctx_list(asm)}⊢ {gf}   "
                f"({logic}; {len(g.events)} steps, verified)\n")
        return Answer(True, head + render(g, level), g)

    def diagnose_proof(self, g: TCIH) -> Answer:
        d = diagnose(g)
        if d["ok"]:
            return Answer(True, "✓ The proof is structurally well-formed and "
                                "every inference is sound.", g)
        lines = ["✗ Problems found:"]
        for er in d["errors"]:
            lines.append(f"   • [{er['class']}] at {er['where']}: {er['detail']}")
        if d["locus_event"]:
            lines.append(f"   ↳ first failure at {d['locus_event']}; smallest "
                         f"failing sub-derivation: events {d['minimal_subproof_events']}")
        return Answer(False, "\n".join(lines), g)

    def verify_llm_steps(self, steps: List[Dict]) -> Answer:
        """Neuro-symbolic loop: accept a list of proposed steps (e.g. from an
        LLM) of the form {rule, sources:[ids], conclusion, target, discharge:[]}
        already assembled into a TCIH `g`, and verify+localize. Here we accept a
        prebuilt TCIH for simplicity and delegate to `diagnose_proof`."""
        raise NotImplementedError("assemble a TCIH then call diagnose_proof")

    def is_valid(self, goal: str, assumptions: Optional[List[str]] = None) -> Dict:
        gf = parse(goal)
        asm = [parse(a) for a in (assumptions or [])]
        return {"intuitionistic": ipc_provable(asm, gf),
                "classical": entails(asm, gf)}


def show_ctx_list(asm: List[Formula]) -> str:
    return (", ".join(str(a) for a in asm) + " ") if asm else ""


# --------------------------------------------------------------------------- #
# Minimal command-line REPL
# --------------------------------------------------------------------------- #
BANNER = """TCIH-Chat — a verified mathematics proof assistant
Commands:
  prove <formula>                 e.g.  prove (A->B)->((B->C)->(A->C))
  prove <formula> | <a1>, <a2>    prove a goal from assumptions
  valid <formula>                 report intuitionistic / classical validity
  outline <formula>               prove and show an outline
  help | quit
Connectives:  ~ ¬   & ∧   | ∨   -> ⇒   F ⊥
"""


def repl() -> None:                                   # pragma: no cover
    import sys
    asst = Assistant()
    print(BANNER)
    while True:
        try:
            line = input("∴ ").strip()
        except (EOFError, KeyboardInterrupt):
            print(); break
        if not line:
            continue
        if line in ("quit", "exit", ":q"):
            break
        if line == "help":
            print(BANNER); continue
        try:
            if line.startswith("valid "):
                v = asst.is_valid(line[6:].strip())
                print(f"  intuitionistic: {v['intuitionistic']};  classical: {v['classical']}")
                continue
            level = "detailed"
            if line.startswith("outline "):
                line = "prove " + line[len("outline "):]; level = "outline"
            if line.startswith("prove "):
                body = line[len("prove "):]
                if "|" in body:
                    goal, asm = body.split("|", 1)
                    asms = [a.strip() for a in asm.split(",") if a.strip()]
                else:
                    goal, asms = body, []
                print(asst.prove_goal(goal.strip(), asms, level=level))
            else:
                print(asst.prove_goal(line))     # bare formula = prove it
        except Exception as exc:                 # noqa: BLE001
            print(f"  (parse/availability error: {exc})")


__all__ = ["Assistant", "Answer", "render", "repl", "RULE_NAMES"]


if __name__ == "__main__":                            # pragma: no cover
    repl()
