"""BSL -> Lean 4 verification obligations (core-only, `omega`-checkable).

Conservation is a *structural* fact about stoichiometry. If an invariant's
covector c lies in the left null space of the stoichiometric matrix N, then for
ANY kinetics

    d/dt (c . x) = c . (N v) = (c . N) v = 0

because each reaction flux v_r enters every species' derivative with its net
stoichiometric coefficient. We emit exactly that statement with each flux as an
opaque integer, so the goal is linear and closes by `omega` in Lean core — no
Mathlib, no real analysis, no axioms.

The check is real: if the declared invariant is *not* a conservation law of the
network, `c . N != 0` for some reaction, the goal is false, and `omega` fails.
"""

from __future__ import annotations

from fractions import Fraction
from math import gcd

from .emit import _net
from ..nodes import Model, Invariant, FluxProperty, exact
from .names import user, internal, comment

D = internal("d")   # common denominator of a homogenized flux vector


def _is_int(x: float) -> bool:
    return x == int(x)


def _term(coeff: int, var: str) -> str:
    if coeff == 1:
        return var
    if coeff == -1:
        return f"-{var}"
    if coeff < 0:
        return f"({coeff}) * {var}"
    return f"{coeff} * {var}"


def _join_plus(parts: list[str]) -> str:
    if not parts:
        return "0"
    out = parts[0]
    for p in parts[1:]:
        out += f" + ({p})" if p.startswith("-") else f" + {p}"
    return out


def _dexpr(model: Model, species: str, relevant: list, scale: int = 1) -> str:
    """`scale · d/dt(species)` as an integer combination of the fluxes."""
    terms = []
    for r in relevant:
        c = _net(r, species) * scale
        if c == 0:
            continue
        terms.append(_term(int(c), f"v_{r.name}"))
    return _join_plus(terms)


def _human(inv: Invariant) -> str:
    return " + ".join(
        (t.species if t.coeff == 1 else f"{_int_or_float(t.coeff)}*{t.species}")
        for t in inv.terms
    )


def _int_or_float(x: float):
    return int(x) if _is_int(x) else x


def obligation(model: Model, inv: Invariant) -> dict:
    """`d/dt(c·x) = 0` as a flux-abstract identity, closed by `omega`.

    Rational coefficients are scaled to integers: with `L1` the LCM of the
    invariant's denominators and `L2` that of the stoichiometry, the emitted
    goal is `Σ (L1·c_i)·(L2·(N v)_i) = 0`, i.e. `L1·L2` times the claim. A
    non-zero multiple of a linear identity holds iff the identity does, and an
    identity holds over ℤ iff it holds over ℝ (its coefficients must vanish).
    """
    expr = _human(inv)
    claim = f"d/dt({expr}) = 0"
    relevant = [
        r for r in model.reactions
        if any(_net(r, t.species) != 0 for t in inv.terms)
    ]
    L1 = _lcm_den([exact(t.coeff) for t in inv.terms])
    L2 = _lcm_den([_net(r, t.species) for r in relevant for t in inv.terms])
    parts = []
    for t in inv.terms:
        c = int(exact(t.coeff) * L1)
        inner = f"({_dexpr(model, t.species, relevant, L2)})"
        if c == 1:
            parts.append(inner)
        elif c == -1:
            parts.append(f"-{inner}")
        else:
            parts.append(f"{c} * {inner}")
    lhs = _join_plus(parts)

    flux_vars = " ".join(f"v_{r.name}" for r in relevant)
    sig = f" ({flux_vars} : Int)" if relevant else ""
    note = (f"-- Scaled by {L1 * L2} to integer coefficients.\n"
            if L1 * L2 != 1 else "")
    body = (
        f"{note}theorem {user(inv.name)}{sig} :\n"
        f"    {lhs} = 0 := by\n"
        f"  omega"
    )
    return {"name": inv.name, "claim": claim, "integer_ok": True, "lean": body}


def _lcm_den(qs) -> int:
    L = 1
    for q in qs:
        L = L * q.denominator // gcd(L, q.denominator)
    return L


def _lin(coeffs: dict, rel: str, d_coeff: Fraction) -> str:
    """Render `Σ coeffs[v]·v  rel  d_coeff·d`, scaled to integer coefficients."""
    L = _lcm_den(list(coeffs.values()) + [d_coeff])
    lhs = _join_plus([_term(int(c * L), v) for v, c in coeffs.items() if c != 0])
    k = int(d_coeff * L)
    rhs = "0" if k == 0 else _term(k, D)
    return f"{lhs} {rel} {rhs}"


def _steady_state_obligation(model: Model, prop: FluxProperty) -> dict:
    """Bound a reaction flux from steady-state flux balance + interval influx.

    At steady state the net flux of each species is zero (`S v = 0`). A
    zeroth-order influx reaction's flux equals its rate constant, so its
    parameter interval bounds that flux. The target bound must follow for
    every REAL flux vector satisfying those linear constraints.

    `omega` decides integer arithmetic, and integer validity does NOT imply
    real validity for a feasibility statement: with `∅ → A`, `2A → B`,
    `B → ∅` and `v_in ∈ [1, 1]`, no integer flux vector exists, so any bound
    would "verify" over ℤ while the real efflux is 0.5. We therefore
    homogenize: every rational flux vector is `v = w / d` with `w ∈ ℤⁿ`,
    `d ∈ ℤ, d > 0`, and multiplying each constraint by `d` keeps it linear
    (constants become multiples of `d`). The obligation quantifies over all
    such `(d, w)`, so it is equivalent to the statement over ℚ. Over ℚ and ℝ
    the statements agree: the counterexamples form a polyhedron with rational
    data, which is empty over ℝ iff it is empty over ℚ. Hence `omega`
    proving the homogenized goal is a proof of the real-valued bound, and a
    failure is a genuine (rational) counterexample.
    """
    lo, hi = exact(prop.lo), exact(prop.hi)
    claim = (f"flux({prop.reaction}) in "
             f"[{_int_or_float(prop.lo)}, {_int_or_float(prop.hi)}] at steady state")

    hyps: list[tuple[str, str]] = [(internal("hd"), f"0 < {D}")]
    for s in model.species:
        coeffs = {f"v_{r.name}": _net(r, s.name) for r in model.reactions}
        if any(c != 0 for c in coeffs.values()):
            hyps.append((f"hs_{s.name}", _lin(coeffs, "=", Fraction(0))))

    pmap = {p.name: p for p in model.params}
    for r in model.reactions:
        if (r.rate_law == "mass_action" and len(r.reactants) == 0
                and r.rate_args and r.rate_args[0].name in pmap):
            p = pmap[r.rate_args[0].name]
            v = {f"v_{r.name}": Fraction(1)}
            hyps.append((f"hin_lo_{r.name}", _lin(v, "≥", exact(p.lo))))
            hyps.append((f"hin_hi_{r.name}", _lin(v, "≤", exact(p.hi))))

    t = {f"v_{prop.reaction}": Fraction(1)}
    goal = f"{_lin(t, '≥', lo)} ∧ {_lin(t, '≤', hi)}"
    flux_vars = " ".join(f"v_{r.name}" for r in model.reactions)
    body = (
        f"-- Homogenized over ℚ: real fluxes are v_r / d' (see verify_emit.py).\n"
        f"theorem {user(prop.name)} ({D} {flux_vars} : Int)"
        + "".join(f"\n    ({hn} : {ln})" for hn, ln in hyps)
        + f" :\n    {goal} := by\n  omega"
    )
    return {"name": prop.name, "claim": claim, "integer_ok": True, "lean": body}


def emit_verification(model: Model) -> tuple[str, list[dict]]:
    """Return (lean_source, obligations): one theorem per declared invariant
    (conservation) and per steady-state flux property."""
    obligations = [obligation(model, inv) for inv in model.invariants]
    if model.steady_state:
        obligations += [_steady_state_obligation(model, p)
                        for p in model.properties]
    L: list[str] = []
    L.append(f"/- Auto-generated conservation obligations for {comment(model.name)} "
             f"by GSK-LeanBio. -/")
    L.append("/- Flux-abstract stoichiometric conservation, checked by `omega` "
             "(Lean core, no Mathlib). -/")
    L.append(f"namespace BSL.{user(model.name)}.Verify")
    L.append("")
    for ob in obligations:
        L.append(ob["lean"])
        L.append("")
    L.append(f"end BSL.{user(model.name)}.Verify")
    L.append("")
    return "\n".join(L), obligations
