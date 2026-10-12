from pathlib import Path

from bsl.parser import parse, parse_file
from bsl.typecheck import check, has_errors

EXAMPLE = Path(__file__).resolve().parents[1] / "examples" / "A-enzyme-kinetics" / "model.bsl"


def codes(text: str):
    return {d.code for d in check(parse(text))}


def test_example_is_clean():
    diags = check(parse_file(EXAMPLE))
    assert not has_errors(diags), [d.format() for d in diags]


def test_undeclared_species():
    src = """model M {
      species A @init 1.0
      reaction r : A -> Z @mass_action(k)
      param k in [0.0, 1.0] @assumed
    }"""
    assert "E_UNDECLARED_SPECIES" in codes(src)


def test_undeclared_param():
    src = """model M {
      species A
      species B
      reaction r : A -> B @mass_action(missing)
    }"""
    assert "E_UNDECLARED_PARAM" in codes(src)


def test_negative_initial():
    src = "model M { species A @init -1.0 }"
    assert "E_NEGATIVE_INITIAL" in codes(src)


def test_negative_rate_and_bad_interval():
    src = """model M {
      species A
      species B
      reaction r : A -> B @mass_action(k)
      param k in [1.0, 0.0] @assumed
      param j in [-1.0, 2.0] @assumed
    }"""
    found = codes(src)
    assert "E_BAD_INTERVAL" in found
    assert "E_NEGATIVE_RATE" in found


def test_unused_param_warning():
    src = """model M {
      species A
      species B
      reaction r : A -> B @mass_action(k)
      param k in [0.0, 1.0] @assumed
      param unused in [0.0, 1.0] @assumed
    }"""
    diags = check(parse(src))
    assert any(d.code == "W_UNUSED_PARAM" for d in diags)
    assert not has_errors(diags)


def test_duplicate_species():
    src = "model M { species A\n species A }"
    assert "E_DUP_SPECIES" in codes(src)


def test_invariant_total_checked_against_initial_state():
    src = """model M {
      species A @init 6.0
      species B @init 4.0
      reaction r : A -> B @mass_action(k)
      param k in [1.0, 2.0] @assumed
      invariant t : A + B = 20.0
    }"""
    assert "E_INVARIANT_INIT_MISMATCH" in codes(src)
    assert "E_INVARIANT_INIT_MISMATCH" not in codes(src.replace("20.0", "10.0"))


def test_invariant_without_init_is_flagged_unanchored():
    src = """model M {
      species A
      species B
      reaction r : A -> B @mass_action(k)
      param k in [1.0, 2.0] @assumed
      invariant t : A + B = 1.0
    }"""
    assert "W_INVARIANT_UNANCHORED" in codes(src)


def test_negative_total_rejected():
    src = """model M {
      species A
      species B
      reaction r : A -> B @mass_action(k)
      param k in [1.0, 2.0] @assumed
      invariant t : A + B = -1.0
    }"""
    assert "E_NEGATIVE_TOTAL" in codes(src)


def test_repeated_invariant_term_warns():
    src = """model M {
      species A @init 1.0
      species B @init 0.0
      reaction r : A -> B @mass_action(k)
      param k in [1.0, 2.0] @assumed
      invariant t : A + A + B = 2.0
    }"""
    assert "W_REPEATED_TERM" in codes(src)
