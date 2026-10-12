from fractions import Fraction
from pathlib import Path

import pytest

from bsl.parser import parse, parse_file
from bsl.certify import classify, certified_bounds, emit_lean_instance, Unsupported

EX = Path(__file__).resolve().parents[1] / "examples"


def test_classify_reversible_example():
    p = classify(parse_file(EX / "E-reversible" / "model.bsl"))
    assert {p.sp_a, p.sp_b} == {"A", "B"}
    assert (p.kf, p.kr) == ("kf", "kr")
    assert p.M == 10
    assert (p.kf_lo, p.kf_hi) == (1, 2)
    assert (p.kr_lo, p.kr_hi) == (3, 4)


def test_certified_bounds_match_flagship():
    p = classify(parse_file(EX / "E-reversible" / "model.bsl"))
    a_lo, a_hi, b_lo, b_hi = certified_bounds(p)
    assert (a_lo, a_hi, b_lo, b_hi) == (6, 8, 2, 4)


def test_emitted_instance_is_flagship_shaped():
    m = parse_file(EX / "E-reversible" / "model.bsl")
    lean = emit_lean_instance(m)
    assert "theorem steady_state_bounds" in lean
    assert "linear_combination hss' + kr' * hmass'" in lean
    assert "nlinarith" in lean
    assert "6 ≤ «A» ∧ «A» ≤ 8 ∧ 2 ≤ «B» ∧ «B» ≤ 4" in lean
    assert "sorry" not in lean


def test_fractional_bounds_emit_rationals():
    # kf∈[1,1], kr∈[1,2], M=1  ->  A* = kr/(1+kr) ∈ [1/2, 2/3]
    src = """model Frac {
      species A @init 0.5
      species B @init 0.5
      reaction f : A -> B @mass_action(kf)
      reaction r : B -> A @mass_action(kr)
      param kf in [1.0, 1.0] @assumed
      param kr in [1.0, 2.0] @assumed
      invariant tot : A + B = 1.0
    }"""
    p = classify(parse(src))
    a_lo, a_hi, _, _ = certified_bounds(p)
    assert a_lo == Fraction(1, 2) and a_hi == Fraction(2, 3)
    assert "(1 / 2 : ℝ)" in emit_lean_instance(parse(src), p)


def test_fail_closed_michaelis_menten():
    with pytest.raises(Unsupported) as e:
        classify(parse_file(EX / "B-michaelis-menten" / "model.bsl"))
    assert e.value.code in {"UnsupportedConstruct", "UnsupportedKineticLaw"}


def test_fail_closed_missing_conservation():
    src = """model NoCons {
      species A @init 1.0
      species B @init 0.0
      reaction f : A -> B @mass_action(kf)
      reaction r : B -> A @mass_action(kr)
      param kf in [1.0, 2.0] @assumed
      param kr in [1.0, 2.0] @assumed
    }"""
    with pytest.raises(Unsupported) as e:
        classify(parse(src))
    assert e.value.code == "MissingConservationLaw"


def test_fail_closed_nonpositive_rate():
    src = """model ZeroRate {
      species A @init 1.0
      species B @init 0.0
      reaction f : A -> B @mass_action(kf)
      reaction r : B -> A @mass_action(kr)
      param kf in [0.0, 2.0] @assumed
      param kr in [1.0, 2.0] @assumed
      invariant tot : A + B = 1.0
    }"""
    with pytest.raises(Unsupported) as e:
        classify(parse(src))
    assert e.value.code == "CannotProvePositiveDenominator"


def _rev(kf, kr, total, init_a="6.0", init_b="4.0"):
    return f"""model R {{
      species A @init {init_a}
      species B @init {init_b}
      reaction f : A -> B @mass_action(kf)
      reaction r : B -> A @mass_action(kr)
      param kf in [{kf[0]}, {kf[1]}] @assumed
      param kr in [{kr[0]}, {kr[1]}] @assumed
      invariant tot : A + B = {total}
    }}"""


def test_nanomolar_total_is_exact_not_rounded_to_zero():
    # 5 nM in molar units used to round to M = 0 and certify A*, B* ∈ [0, 0].
    src = _rev(("1.0", "2.0"), ("3.0", "4.0"), "5.0e-9", "3.0e-9", "2.0e-9")
    p = classify(parse(src))
    assert p.M == Fraction(5, 10**9)
    a_lo, a_hi, _, _ = certified_bounds(p)
    assert (a_lo, a_hi) == (Fraction(3, 10**9), Fraction(4, 10**9))


def test_slow_rate_constant_is_exact_not_rounded_to_zero():
    # kf ∈ [1e-7, 2e-7] used to become kf ∈ [0, 0] and certify A* = 10.
    p = classify(parse(_rev(("1.0e-7", "2.0e-7"), ("3.0", "4.0"), "10.0")))
    assert p.kf_lo == Fraction(1, 10**7) and p.kf_hi == Fraction(2, 10**7)
    a_lo, a_hi, _, _ = certified_bounds(p)
    assert a_lo < 10 and a_hi < 10


def test_bounds_with_many_significant_digits_are_not_rounded():
    # kf_hi = 2.0000004 used to round to 2, so the certified A* lower bound
    # (6) excluded the model's own corner A* = 30/5.0000004.
    p = classify(parse(_rev(("1.0", "2.0000004"), ("3.0", "4.0"), "10.0")))
    a_lo, _, _, _ = certified_bounds(p)
    assert a_lo == Fraction(30) / (Fraction("2.0000004") + 3)
    assert a_lo < 6


def test_tiny_rates_on_both_sides_do_not_crash():
    # Both lower bounds used to round to 0 -> ZeroDivisionError.
    p = classify(parse(_rev(("1.0e-7", "2.0e-7"), ("3.0e-7", "4.0e-7"), "10.0")))
    a_lo, a_hi, _, _ = certified_bounds(p)
    assert 0 < a_lo <= a_hi < 10


def test_huge_bound_does_not_crash():
    # 1e400 overflows a float; it used to raise OverflowError.
    p = classify(parse(_rev(("1.0", "1e400"), ("3.0", "4.0"), "10.0")))
    assert p.kf_hi == 10**400
    emit_lean_instance(parse(_rev(("1.0", "1e400"), ("3.0", "4.0"), "10.0")), p)


def test_species_named_like_binders_cannot_shadow_them():
    # Species `kr`/`kf` used to shadow the rate-constant binders, turning
    # `hss` into `kf * kr = kr * kf` and the hypotheses into a contradiction.
    src = """model Shadow {
      species kr @init 6.0
      species kf @init 4.0
      reaction forward : kr -> kf @mass_action(p)
      reaction reverse : kf -> kr @mass_action(q)
      param p in [1.0, 2.0] @assumed
      param q in [3.0, 4.0] @assumed
      invariant total : kr + kf = 10.0
    }"""
    lean = emit_lean_instance(parse(src))
    assert "(kf' kr' «kr» «kf» : ℝ)" in lean
    assert "(hss' : kf' * «kr» = kr' * «kf»)" in lean


def test_repeated_invariant_terms_are_summed_not_collapsed():
    # `A + A + B` is 2A + B. It used to be read as A + B and certified.
    src = _rev(("1.0", "2.0"), ("3.0", "4.0"), "10.0", "2.0", "6.0").replace(
        "invariant tot : A + B", "invariant tot : A + A + B")
    with pytest.raises(Unsupported) as e:
        classify(parse(src))
    assert e.value.code == "MissingConservationLaw"


def test_total_must_match_initial_state():
    # Initial total is 10; certifying with 20 described unreachable states.
    with pytest.raises(Unsupported) as e:
        classify(parse(_rev(("1.0", "2.0"), ("3.0", "4.0"), "20.0")))
    assert e.value.code == "InconsistentConservationLaw"
