from pathlib import Path

import pytest

from bsl.parser import parse, parse_file
from bsl.lexer import BSLError

EXAMPLE = Path(__file__).resolve().parents[1] / "examples" / "A-enzyme-kinetics" / "model.bsl"


def test_parse_example():
    model = parse_file(EXAMPLE)
    assert model.name == "EnzymeKinetics"
    assert [s.name for s in model.species] == ["E", "S", "ES", "P"]
    assert [r.name for r in model.reactions] == ["binding", "unbinding", "catalysis"]
    assert {p.name for p in model.params} == {"kf", "kr", "kcat"}
    assert [i.name for i in model.invariants] == ["enzyme_conservation"]


def test_species_initial():
    model = parse_file(EXAMPLE)
    init = {s.name: s.initial for s in model.species}
    assert init == {"E": 1.0, "S": 10.0, "ES": 0.0, "P": 0.0}


def test_reaction_stoichiometry():
    model = parse_file(EXAMPLE)
    binding = next(r for r in model.reactions if r.name == "binding")
    assert {ref.species for ref in binding.reactants} == {"E", "S"}
    assert [ref.species for ref in binding.products] == ["ES"]
    assert binding.rate_law == "mass_action"
    assert binding.rate_param_names() == ["kf"]


def test_param_grades():
    model = parse_file(EXAMPLE)
    by_name = {p.name: p for p in model.params}
    assert by_name["kcat"].grade == "DERIVED_FROM_EXPERIMENT"
    assert by_name["kcat"].grade_meta == {"replicates": 3, "p": 0.01}
    assert by_name["kf"].grade == "LITERATURE_CONSENSUS"
    assert by_name["kf"].grade_meta == {"citations": 12}
    assert by_name["kr"].grade == "ASSUMED_FOR_MODELING"


def test_evidence_byte_ranges_roundtrip():
    """Every span must point at the exact bytes it claims to."""
    model = parse_file(EXAMPLE)
    data = model.source.data
    for s in model.species:
        sub = data[s.span.byte_start:s.span.byte_end].decode("utf-8")
        assert sub == s.span.text
        assert s.name in sub


def test_scientific_notation():
    model = parse("model M { param k in [9.0e5, 1.1e6] @assumed\n"
                  " reaction r : A -> B @mass_action(k)\n species A\n species B }")
    p = model.params[0]
    assert p.lo == 9.0e5
    assert p.hi == 1.1e6


def test_syntax_error_has_position():
    with pytest.raises(BSLError) as exc:
        parse("model M { species }")  # missing species name
    assert exc.value.line == 1


def test_trailing_content_after_model_is_an_error():
    # It used to be ignored while still covered by the source hash.
    with pytest.raises(BSLError):
        parse("model M { species A } species B reaction junk")


def test_cr_only_line_endings():
    m = parse("model M {\r  # note\r  species A\r}\r")
    assert [s.name for s in m.species] == ["A"]
    assert m.species[0].span.line == 3


def test_crlf_lines_counted_once():
    m = parse("model M {\r\n  species A\r\n}\r\n")
    assert m.species[0].span.line == 2


def test_utf8_bom_accepted_and_hashed(tmp_path):
    import hashlib
    data = b"\xef\xbb\xbfmodel M { species A }"
    f = tmp_path / "bom.bsl"
    f.write_bytes(data)
    m = parse_file(f)
    assert m.source.sha256 == hashlib.sha256(data).hexdigest()


def test_invalid_utf8_is_a_bsl_error(tmp_path):
    f = tmp_path / "bad.bsl"
    f.write_bytes(b"model M {\n species \xff }")
    with pytest.raises(BSLError) as e:
        parse_file(f)
    assert e.value.line == 2


def test_source_hash_is_of_the_exact_file_bytes(tmp_path):
    import hashlib
    data = b"model M {\r\n  species A\r\n}\r\n"
    f = tmp_path / "crlf.bsl"
    f.write_bytes(data)
    assert parse_file(f).source.sha256 == hashlib.sha256(data).hexdigest()
