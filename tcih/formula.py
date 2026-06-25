"""Propositional formula AST, substitution, parsing and metrics for TCIH.

The corrected TCIH framework (see the accompanying paper, Section 3) is developed
over the implicational--conjunctive--disjunctive fragment of intuitionistic
propositional logic with falsum,

    phi ::= bot | p | not phi | phi and phi | phi or phi | phi => phi

Schema variables are ordinary atoms (by convention single upper-case letters
A, B, C, ...) that may be instantiated by a substitution ``Subst`` when a rule
schema is turned into a rule instance R[sigma] (Definition 3.3 in the paper).

The module is deliberately dependency-free (standard library only) so that the
structural core can be archived as a self-contained reference implementation.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, Iterable, List, Tuple

# ---------------------------------------------------------------------------
# Abstract syntax
# ---------------------------------------------------------------------------


class Formula:
    """Base class for propositional formulas (immutable, hashable)."""


    # size = number of AST nodes; used for the encoded input size N of Thm 5.x
    def size(self) -> int:
        raise NotImplementedError

    def atoms(self) -> "frozenset[str]":
        raise NotImplementedError


@dataclass(frozen=True)
class Bot(Formula):
    """Falsum (the absurd proposition)."""


    def __str__(self) -> str:
        return "⊥"  # ⊥

    def size(self) -> int:
        return 1

    def atoms(self) -> "frozenset[str]":
        return frozenset()


@dataclass(frozen=True)
class Atom(Formula):
    name: str

    def __str__(self) -> str:
        return self.name

    def size(self) -> int:
        return 1

    def atoms(self) -> "frozenset[str]":
        return frozenset({self.name})


@dataclass(frozen=True)
class Not(Formula):
    sub: Formula

    def __str__(self) -> str:
        return _fmt(self, 0)

    def size(self) -> int:
        return 1 + self.sub.size()

    def atoms(self) -> "frozenset[str]":
        return self.sub.atoms()


@dataclass(frozen=True)
class And(Formula):
    left: Formula
    right: Formula

    def __str__(self) -> str:
        return _fmt(self, 0)

    def size(self) -> int:
        return 1 + self.left.size() + self.right.size()

    def atoms(self) -> "frozenset[str]":
        return self.left.atoms() | self.right.atoms()


@dataclass(frozen=True)
class Or(Formula):
    left: Formula
    right: Formula

    def __str__(self) -> str:
        return _fmt(self, 0)

    def size(self) -> int:
        return 1 + self.left.size() + self.right.size()

    def atoms(self) -> "frozenset[str]":
        return self.left.atoms() | self.right.atoms()


@dataclass(frozen=True)
class Imp(Formula):
    left: Formula
    right: Formula

    def __str__(self) -> str:
        return _fmt(self, 0)

    def size(self) -> int:
        return 1 + self.left.size() + self.right.size()

    def atoms(self) -> "frozenset[str]":
        return self.left.atoms() | self.right.atoms()


# Convenient constructors -----------------------------------------------------

BOT = Bot()


def neg(p: Formula) -> Formula:
    return Not(p)


def land(*ps: Formula) -> Formula:
    it = iter(ps)
    acc = next(it)
    for p in it:
        acc = And(acc, p)
    return acc


def lor(*ps: Formula) -> Formula:
    it = iter(ps)
    acc = next(it)
    for p in it:
        acc = Or(acc, p)
    return acc


def imp(a: Formula, b: Formula) -> Formula:
    return Imp(a, b)


# ---------------------------------------------------------------------------
# Substitution (schema -> instance)
# ---------------------------------------------------------------------------

Subst = Dict[str, Formula]


def apply_subst(phi: Formula, sigma: Subst) -> Formula:
    """Capture-free substitution of atoms by formulas (propositional case)."""
    if isinstance(phi, Bot):
        return phi
    if isinstance(phi, Atom):
        return sigma.get(phi.name, phi)
    if isinstance(phi, Not):
        return Not(apply_subst(phi.sub, sigma))
    if isinstance(phi, And):
        return And(apply_subst(phi.left, sigma), apply_subst(phi.right, sigma))
    if isinstance(phi, Or):
        return Or(apply_subst(phi.left, sigma), apply_subst(phi.right, sigma))
    if isinstance(phi, Imp):
        return Imp(apply_subst(phi.left, sigma), apply_subst(phi.right, sigma))
    raise TypeError(f"unknown formula {phi!r}")


def match(pattern: Formula, target: Formula, sigma: Subst | None = None) -> Subst | None:
    """One-way (schema) matching: find sigma with apply_subst(pattern, sigma)==target.

    Returns the (extended) substitution, or None if no match. Schema variables
    are *all* atoms of ``pattern``; a non-atomic pattern node must match the same
    constructor in ``target``.
    """
    if sigma is None:
        sigma = {}
    if isinstance(pattern, Atom):
        bound = sigma.get(pattern.name)
        if bound is None:
            sigma = dict(sigma)
            sigma[pattern.name] = target
            return sigma
        return sigma if bound == target else None
    if isinstance(pattern, Bot):
        return sigma if isinstance(target, Bot) else None
    if isinstance(pattern, Not) and isinstance(target, Not):
        return match(pattern.sub, target.sub, sigma)
    for cls in (And, Or, Imp):
        if isinstance(pattern, cls) and isinstance(target, cls):
            s2 = match(pattern.left, target.left, sigma)  # type: ignore[attr-defined]
            if s2 is None:
                return None
            return match(pattern.right, target.right, s2)  # type: ignore[attr-defined]
    return None


# ---------------------------------------------------------------------------
# Parser (for the chatbot front-end and tests)
# ---------------------------------------------------------------------------
# Grammar (precedence: not > and > or > imp; imp right-assoc):
#   imp   := orf ('->' imp)?
#   orf   := andf ('|' andf)*
#   andf  := unary ('&' unary)*
#   unary := '~' unary | atom | '(' imp ')' | 'F'/'_|_' (falsum)
#
# Accepted ASCII/Unicode tokens:
#   not: ~ ! ¬        and: & ∧ /\        or: | ∨ \/
#   imp: -> => ⇒ ⊃    falsum: F ⊥ #false

_TOKENS = {
    "->": "IMP", "=>": "IMP", "⇒": "IMP", "⊃": "IMP",
    "&": "AND", "∧": "AND", "/\\": "AND",
    "|": "OR", "∨": "OR", "\\/": "OR",
    "~": "NOT", "!": "NOT", "¬": "NOT",
    "(": "LP", ")": "RP",
}


def _tokenize(s: str) -> List[Tuple[str, str]]:
    out: List[Tuple[str, str]] = []
    i, n = 0, len(s)
    while i < n:
        c = s[i]
        if c.isspace():
            i += 1
            continue
        two = s[i : i + 2]
        if two in _TOKENS:
            out.append((_TOKENS[two], two))
            i += 2
            continue
        if c in _TOKENS:
            out.append((_TOKENS[c], c))
            i += 1
            continue
        if c == "⊥":  # ⊥
            out.append(("BOT", c))
            i += 1
            continue
        if c.isalnum() or c == "_":
            j = i
            while j < n and (s[j].isalnum() or s[j] == "_"):
                j += 1
            word = s[i:j]
            if word in {"F", "false", "False", "FALSE"}:
                out.append(("BOT", word))
            else:
                out.append(("ATOM", word))
            i = j
            continue
        raise ValueError(f"unexpected character {c!r} in {s!r}")
    return out


class _Parser:
    def __init__(self, toks: List[Tuple[str, str]]):
        self.toks = toks
        self.i = 0

    def peek(self) -> str | None:
        return self.toks[self.i][0] if self.i < len(self.toks) else None

    def eat(self, kind: str) -> Tuple[str, str]:
        if self.peek() != kind:
            raise ValueError(f"expected {kind}, got {self.peek()}")
        t = self.toks[self.i]
        self.i += 1
        return t

    def parse(self) -> Formula:
        f = self.imp()
        if self.i != len(self.toks):
            raise ValueError("trailing tokens")
        return f

    def imp(self) -> Formula:
        left = self.orf()
        if self.peek() == "IMP":
            self.eat("IMP")
            return Imp(left, self.imp())
        return left

    def orf(self) -> Formula:
        left = self.andf()
        while self.peek() == "OR":
            self.eat("OR")
            left = Or(left, self.andf())
        return left

    def andf(self) -> Formula:
        left = self.unary()
        while self.peek() == "AND":
            self.eat("AND")
            left = And(left, self.unary())
        return left

    def unary(self) -> Formula:
        k = self.peek()
        if k == "NOT":
            self.eat("NOT")
            return Not(self.unary())
        if k == "LP":
            self.eat("LP")
            f = self.imp()
            self.eat("RP")
            return f
        if k == "BOT":
            self.eat("BOT")
            return BOT
        if k == "ATOM":
            return Atom(self.eat("ATOM")[1])
        raise ValueError(f"unexpected token {k}")


def parse(s: str) -> Formula:
    """Parse a formula from ASCII or Unicode notation. E.g. parse('A -> A')."""
    return _Parser(_tokenize(s)).parse()


def _fmt(f: Formula, parent_prec: int) -> str:
    """Precedence-aware pretty printer with minimal parentheses.

    Precedence: ¬ (4) > ∧ (3) > ∨ (2) > ⇒ (1); ⇒ is right-associative,
    ∧ and ∨ are left-associative.
    """
    if isinstance(f, Bot):
        return "⊥"
    if isinstance(f, Atom):
        return f.name
    if isinstance(f, Not):
        return "¬" + _fmt(f.sub, 4)
    if isinstance(f, And):
        s = _fmt(f.left, 3) + " ∧ " + _fmt(f.right, 4)
        return f"({s})" if parent_prec > 3 else s
    if isinstance(f, Or):
        s = _fmt(f.left, 2) + " ∨ " + _fmt(f.right, 3)
        return f"({s})" if parent_prec > 2 else s
    if isinstance(f, Imp):
        s = _fmt(f.left, 2) + " ⇒ " + _fmt(f.right, 1)
        return f"({s})" if parent_prec > 1 else s
    raise TypeError(f"unknown formula {f!r}")


__all__ = [
    "Formula", "Bot", "Atom", "Not", "And", "Or", "Imp", "BOT",
    "neg", "land", "lor", "imp", "Subst", "apply_subst", "match", "parse",
]
