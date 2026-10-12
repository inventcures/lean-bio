"""Certified-subset recognizer + Lean instantiator.

This is the demo->system step: instead of hand-writing one proof, we hardcode a
*theorem schema* (the verified reversible two-species mass-action steady state,
see `lean/BslLean/ReversibleTwoSpecies.lean`) and instantiate it for any model
that fits the certified subset. Anything outside the subset fails closed with a
precise reason and emits no Lean — that is how the system stays honest.

Certified subset (v0): exactly two species `A`, `B`; exactly two unit-stoichiometry
mass-action reactions forming an inverse pair `A -> B` and `B -> A`; a declared
conservation invariant `A + B = M`; strictly positive rate-constant lower bounds.
"""

from __future__ import annotations

import os
import re
import shutil
import subprocess
import tempfile
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path

from .nodes import Model, exact
from .lean.names import user, internal, comment


class Unsupported(Exception):
    """Raised when a model is outside the certified subset (fail closed)."""

    def __init__(self, code: str, message: str):
        super().__init__(f"{code}: {message}")
        self.code = code
        self.message = message


@dataclass
class ReversiblePattern:
    sp_a: str
    sp_b: str
    kf: str            # forward rate-constant parameter
    kr: str            # reverse rate-constant parameter
    M: Fraction
    kf_lo: Fraction
    kf_hi: Fraction
    kr_lo: Fraction
    kr_hi: Fraction


def classify(model: Model) -> ReversiblePattern:
    if len(model.species) != 2:
        raise Unsupported("UnsupportedConstruct",
                          f"expected 2 species, found {len(model.species)}")
    if len(model.reactions) != 2:
        raise Unsupported("UnsupportedConstruct",
                          f"expected 2 reactions, found {len(model.reactions)}")

    for r in model.reactions:
        if r.rate_law != "mass_action":
            raise Unsupported("UnsupportedKineticLaw",
                              f"reaction {r.name!r} uses {r.rate_law}, "
                              f"expected mass_action")
        if len(r.reactants) != 1 or len(r.products) != 1:
            raise Unsupported("UnsupportedConstruct",
                              f"reaction {r.name!r} is not single-reactant/"
                              f"single-product")
        if r.reactants[0].coeff != 1 or r.products[0].coeff != 1:
            raise Unsupported("UnsupportedConstruct",
                              f"reaction {r.name!r} has non-unit stoichiometry")

    r1, r2 = model.reactions
    a1, b1 = r1.reactants[0].species, r1.products[0].species
    a2, b2 = r2.reactants[0].species, r2.products[0].species
    if not (a1 == b2 and b1 == a2 and a1 != b1):
        raise Unsupported("UnsupportedConstruct",
                          "reactions are not an inverse pair A ⇌ B")
    sp_a, sp_b = a1, b1
    kf, kr = r1.rate_args[0].name, r2.rate_args[0].name
    if kf is None or kr is None:
        raise Unsupported("UnsupportedKineticLaw",
                          "rate constants must be declared parameters")

    M = None
    for inv in model.invariants:
        terms: dict[str, Fraction] = {}
        for t in inv.terms:  # `A + A + B` is 2A + B, not A + B
            terms[t.species] = terms.get(t.species, Fraction(0)) + exact(t.coeff)
        if set(terms) == {sp_a, sp_b} and terms[sp_a] == 1 and terms[sp_b] == 1:
            M = exact(inv.rhs)
            break
    if M is None:
        raise Unsupported("MissingConservationLaw",
                          f"need an invariant {sp_a} + {sp_b} = M")

    init = {s.name: s for s in model.species}
    if init[sp_a].has_init and init[sp_b].has_init:
        if exact(init[sp_a].initial) + exact(init[sp_b].initial) != M:
            raise Unsupported("InconsistentConservationLaw",
                              f"{sp_a} + {sp_b} = {M} contradicts the initial "
                              f"state; the certified bounds would describe "
                              f"unreachable states")
    if M < 0:
        raise Unsupported("InconsistentConservationLaw",
                          f"total {M} is negative")

    pmap = {p.name: p for p in model.params}
    if kf not in pmap or kr not in pmap:
        raise Unsupported("UnsupportedConstruct",
                          "rate parameters are not declared")
    pf, pr = pmap[kf], pmap[kr]
    # Exact rationals from the source text. Never round: a float rounded to a
    # small denominator turns 1e-7 into 0 and silently changes the model.
    kf_lo, kf_hi = exact(pf.lo), exact(pf.hi)
    kr_lo, kr_hi = exact(pr.lo), exact(pr.hi)
    if not (kf_lo > 0 and kr_lo > 0):
        raise Unsupported("CannotProvePositiveDenominator",
                          "rate-constant lower bounds must be strictly positive")

    return ReversiblePattern(
        sp_a=sp_a, sp_b=sp_b, kf=kf, kr=kr, M=M,
        kf_lo=kf_lo, kf_hi=kf_hi,
        kr_lo=kr_lo, kr_hi=kr_hi,
    )


def certified_bounds(p: ReversiblePattern):
    """Tight steady-state intervals. A* = M·kr/(kf+kr) is increasing in kr and
    decreasing in kf, so its extremes sit at opposite corners of the box."""
    a_lo = p.M * p.kr_lo / (p.kf_hi + p.kr_lo)
    a_hi = p.M * p.kr_hi / (p.kf_lo + p.kr_hi)
    b_lo = p.M - a_hi
    b_hi = p.M - a_lo
    return a_lo, a_hi, b_lo, b_hi


def _lit(x: Fraction) -> str:
    x = Fraction(x)
    return str(x.numerator) if x.denominator == 1 else f"({x.numerator} / {x.denominator} : ℝ)"


def emit_lean_instance(model: Model, p: ReversiblePattern | None = None) -> str:
    """The model's certificate: a direct application of the general, kernel-
    checked `BSL.ReversibleTwoSpecies.schema` to this model's numbers.

    The steady state is `IsSteadyState` (a zero of the mass-action vector
    field defined in Lean), not a hand-written equation, and the only proof
    work left per model is `norm_num` evaluating rational arithmetic.
    """
    p = p or classify(model)
    a_lo, a_hi, b_lo, b_hi = certified_bounds(p)
    # User names are «escaped»; emitter binders end in `'`, which no BSL name
    # can contain, so a species named `kf` cannot shadow the rate constant.
    A, B = user(p.sp_a), user(p.sp_b)
    kf, kr = internal("kf"), internal("kr")
    lit = _lit
    args = " ".join(lit(x) for x in (p.kf_lo, p.kf_hi, p.kr_lo, p.kr_hi, p.M))
    L = [
        "import BslLean.ReversibleTwoSpecies",
        "",
        f"/- Auto-generated from {comment(model.source.name)} by `bsl certify`. -/",
        "/- Instance of the general schema BSL.ReversibleTwoSpecies.schema. -/",
        f"namespace BSL.Generated.{user(model.name)}",
        "",
        "open BSL.ReversibleTwoSpecies in",
        f"theorem steady_state_bounds ({kf} {kr} {A} {B} : ℝ)",
        f"    (hkf' : {lit(p.kf_lo)} ≤ {kf} ∧ {kf} ≤ {lit(p.kf_hi)})",
        f"    (hkr' : {lit(p.kr_lo)} ≤ {kr} ∧ {kr} ≤ {lit(p.kr_hi)})",
        f"    (hmass' : {A} + {B} = {lit(p.M)})",
        f"    (hss' : IsSteadyState {kf} {kr} {A} {B}) :",
        f"    {lit(a_lo)} ≤ {A} ∧ {A} ≤ {lit(a_hi)} ∧ "
        f"{lit(b_lo)} ≤ {B} ∧ {B} ≤ {lit(b_hi)} := by",
        f"  obtain ⟨h1', h2', h3', h4'⟩ := schema {args} {kf} {kr} {A} {B}",
        "    (by norm_num) (by norm_num) (by norm_num) hkf' hkr' hmass' hss'",
        "  exact ⟨le_trans (le_of_eq (by norm_num)) h1', le_trans h2' (le_of_eq (by norm_num)),",
        "    le_trans (le_of_eq (by norm_num)) h3', le_trans h4' (le_of_eq (by norm_num))⟩",
        "",
        f"end BSL.Generated.{user(model.name)}",
        "",
    ]
    return "\n".join(L)


# --- kernel check ------------------------------------------------------------

STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def default_lean_project() -> Path | None:
    """The repo's `lean/` Lake project, when running from a checkout."""
    cand = Path(__file__).resolve().parents[1] / "lean"
    return cand if (cand / "lakefile.toml").exists() else None


def find_lake(explicit: str | None = None) -> str | None:
    for cand in (explicit, os.environ.get("BSL_LAKE")):
        if cand and Path(cand).exists():
            return cand
    found = shutil.which("lake")
    if found:
        return found
    for lean in (os.environ.get("BSL_LEAN"),):
        if lean and (Path(lean).parent / "lake").exists():
            return str(Path(lean).parent / "lake")
    elan = Path.home() / ".elan" / "bin" / "lake"
    return str(elan) if elan.exists() else None


@dataclass
class KernelResult:
    ok: bool
    axioms: list[str]
    output: str


def kernel_check(model: Model, lean_text: str, project: Path, lake: str,
                 timeout: int = 1800) -> KernelResult:
    """Kernel-check a generated instance inside the Lake project, then audit
    its axioms. `ok` only if Lean accepts the file AND the theorem depends on
    nothing beyond Lean's standard axioms (no `sorry`, no custom `axiom`)."""
    build = subprocess.run([lake, "build", "BslLean.ReversibleTwoSpecies"],
                           cwd=project, capture_output=True, text=True,
                           timeout=timeout)
    if build.returncode != 0:
        return KernelResult(False, [], (build.stdout + build.stderr).strip())
    thm = f"BSL.Generated.{user(model.name)}.steady_state_bounds"
    with tempfile.TemporaryDirectory() as td:
        f = Path(td) / "Check.lean"
        f.write_text(lean_text + f"\n#print axioms {thm}\n", encoding="utf-8")
        proc = subprocess.run([lake, "env", "lean", str(f)], cwd=project,
                              capture_output=True, text=True, timeout=timeout)
    out = (proc.stdout + proc.stderr).strip()
    axioms: list[str] = []
    m = re.search(r"depends on axioms: \[(.*?)\]", out, re.S)
    if m:
        axioms = [a.strip() for a in m.group(1).split(",") if a.strip()]
    clean = "does not depend on any axioms" in out or (
        m is not None and set(axioms) <= STANDARD_AXIOMS)
    ok = proc.returncode == 0 and clean
    return KernelResult(ok, axioms, out)
