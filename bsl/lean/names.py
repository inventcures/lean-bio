"""Identifier hygiene for emitted Lean.

User names (species, parameters, reactions, invariants, models) are pasted
into Lean source, so two things can go wrong:

* a name that is a Lean keyword (`end`, `fun`, `at`, ...) is a parse error,
  which a journal would misreport as a refuted claim; and
* a name equal to one of the emitter's own binders (`kf`, `p`, `x`, `d`, ...)
  silently shadows it and changes what the theorem says. Species named `kf`
  and `kr` once turned the certified steady-state theorem into a vacuous one.

`user()` wraps every user name in Lean's «guillemets», which accept any
identifier, keywords included. Internal binders end in `'` (see `internal`),
which no BSL identifier can contain, so they can never collide.
"""

from __future__ import annotations


def user(name: str) -> str:
    """A user-supplied identifier, safe to paste anywhere in Lean."""
    return f"«{name}»"


def internal(name: str) -> str:
    """An emitter-owned binder name, disjoint from every BSL identifier."""
    return f"{name}'"


def comment(text: str) -> str:
    """Text safe inside a `/- ... -/` block comment (cannot close or nest it)."""
    return text.replace("-/", "- /").replace("/-", "/ -")
