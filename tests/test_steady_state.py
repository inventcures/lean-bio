from pathlib import Path

import pytest

from bsl.parser import parse, parse_file
from bsl.typecheck import check, has_errors
from bsl.verify import run_verification, find_lean

EX = Path(__file__).resolve().parents[1] / "examples"
LEAN_MISSING = find_lean() is None
needs_lean = pytest.mark.skipif(LEAN_MISSING, reason="no Lean toolchain available")


def test_sources_and_sinks_parse():
    m = parse_file(EX / "D-linear-pathway" / "model.bsl")
    influx = next(r for r in m.reactions if r.name == "influx")
    efflux = next(r for r in m.reactions if r.name == "efflux")
    assert influx.reactants == []                       # source
    assert [p.species for p in influx.products] == ["A"]
    assert efflux.products == []                        # sink
    assert m.steady_state is True
    assert m.properties[0].name == "efflux_in_band"
    assert m.properties[0].reaction == "efflux"


def test_example_d_checks_clean():
    diags = check(parse_file(EX / "D-linear-pathway" / "model.bsl"))
    assert not has_errors(diags), [d.format() for d in diags]


def test_property_without_steady_state_errors():
    src = """model M {
      species A
      species B
      reaction influx :  -> A @mass_action(vin)
      reaction step   : A -> B @mass_action(k1)
      reaction efflux : B ->  @mass_action(k2)
      param vin in [1.0, 2.0] @assumed
      param k1  in [1.0, 2.0] @assumed
      param k2  in [1.0, 2.0] @assumed
      property p : flux(efflux) in [1.0, 2.0]
    }"""
    assert "E_PROPERTY_NEEDS_STEADY_STATE" in {d.code for d in check(parse(src))}


def test_property_unknown_reaction_errors():
    src = """model M {
      species A
      reaction influx : -> A @mass_action(vin)
      param vin in [1.0, 2.0] @assumed
      steady_state
      property p : flux(ghost) in [1.0, 2.0]
    }"""
    assert "E_UNDECLARED_REACTION" in {d.code for d in check(parse(src))}


@needs_lean
def test_steady_state_flux_bound_discharged(tmp_path):
    m = parse_file(EX / "D-linear-pathway" / "model.bsl")
    journal, _ = run_verification(m, tmp_path)
    assert journal["result"] == "verified", journal
    assert journal["obligations"][0]["status"] == "discharged"


@needs_lean
def test_too_tight_flux_band_refuted(tmp_path):
    src = """model M {
      species A
      species B
      reaction influx :  -> A @mass_action(vin)
      reaction step   : A -> B @mass_action(k1)
      reaction efflux : B ->  @mass_action(k2)
      param vin in [10.0, 20.0] @assumed
      param k1  in [1.0, 5.0]   @assumed
      param k2  in [1.0, 5.0]   @assumed
      steady_state
      property too_tight : flux(efflux) in [10.0, 15.0]
    }"""
    journal, _ = run_verification(parse(src), tmp_path)
    assert journal["result"] == "failed"


_PARITY = """model P {{
  species A
  species B
  reaction influx : -> A @mass_action(vin)
  reaction dimer  : 2 A -> B @mass_action(k1)
  reaction efflux : B -> @mass_action(k2)
  param vin in [{vlo}, {vhi}] @assumed
  param k1  in [1.0, 2.0] @assumed
  param k2  in [1.0, 2.0] @assumed
  steady_state
  property p : flux(efflux) in [{lo}, {hi}]
}}"""


@needs_lean
def test_integer_only_band_is_refuted_over_the_reals(tmp_path):
    # Over ℤ, v_in = 2·v_dimer forces v_in = 2 and efflux = 1. Over ℝ the
    # efflux is v_in / 2 ∈ [0.5, 1.5], so "efflux = 1" must NOT verify.
    src = _PARITY.format(vlo="1.0", vhi="3.0", lo="1.0", hi="1.0")
    journal, _ = run_verification(parse(src), tmp_path)
    assert journal["result"] == "failed", journal


@needs_lean
def test_integer_infeasible_system_does_not_prove_anything(tmp_path):
    # v_in = 1 has no integer solution of v_in = 2·v_dimer; ex falso used to
    # "verify" efflux ∈ [100, 200]. The real efflux is 0.5.
    src = _PARITY.format(vlo="1.0", vhi="1.0", lo="100.0", hi="200.0")
    journal, _ = run_verification(parse(src), tmp_path)
    assert journal["result"] == "failed", journal


@needs_lean
def test_fractional_band_verifies_over_the_reals(tmp_path):
    src = _PARITY.format(vlo="1.0", vhi="3.0", lo="0.5", hi="1.5")
    journal, _ = run_verification(parse(src), tmp_path)
    assert journal["result"] == "verified", journal
