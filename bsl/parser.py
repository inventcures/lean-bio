"""Recursive-descent parser: tokens -> Model AST.

Grammar (informal):

    model       := "model" NAME "{" decl* "}"
    decl        := species | reaction | param | invariant
    species     := "species" NAME ("@" "init" NUMBER)?
    reaction    := "reaction" NAME ":" side "->" side "@" NAME "(" NAME ")"
    side        := term ("+" term)*
    term        := NUMBER? NAME
    param       := "param" NAME "in" "[" NUMBER "," NUMBER "]" grade?
    grade       := "@" "experiment" "(" "replicates" "=" NUMBER "," "p" "=" NUMBER ")"
                 | "@" "literature" "(" "citations" "=" NUMBER ")"
                 | "@" "assumed"
    invariant   := "invariant" NAME ":" side "=" NUMBER
"""

from __future__ import annotations

from pathlib import Path

from .lexer import Token, tokenize, BSLError
from .nodes import (
    Model,
    Species,
    Reaction,
    SpeciesRef,
    Param,
    Invariant,
    FluxProperty,
    Num,
    Source,
    RateArg,
    KNOWN_RATE_LAWS,
    RATE_LAW_ARITY,
    GRADE_EXPERIMENT,
    GRADE_LITERATURE,
    GRADE_ASSUMED,
)


class _Parser:
    def __init__(self, toks: list[Token], src: Source):
        self.toks = toks
        self.src = src
        self.pos = 0

    # --- token stream helpers -------------------------------------------------
    @property
    def cur(self) -> Token:
        return self.toks[self.pos]

    def advance(self) -> Token:
        t = self.toks[self.pos]
        if t.kind != "EOF":
            self.pos += 1
        return t

    def at(self, kind: str) -> bool:
        return self.cur.kind == kind

    def at_kw(self, word: str) -> bool:
        return self.cur.kind == "NAME" and self.cur.value == word

    def expect(self, kind: str) -> Token:
        if self.cur.kind != kind:
            self._err(f"expected {kind!r}, found {self._desc(self.cur)}")
        return self.advance()

    def expect_kw(self, word: str) -> Token:
        if not self.at_kw(word):
            self._err(f"expected keyword {word!r}, found {self._desc(self.cur)}")
        return self.advance()

    def _desc(self, t: Token) -> str:
        if t.kind == "EOF":
            return "end of input"
        return f"{t.value!r}"

    def _err(self, msg: str) -> None:
        raise BSLError(msg, self.cur.line, self.cur.col)

    def _span(self, start: Token, end: Token):
        return self.src.span(start.cstart, end.cend, start.line, start.col)

    def _number(self) -> tuple[Num, Token]:
        t = self.expect("NUMBER")
        return Num(t.value), t

    # --- grammar --------------------------------------------------------------
    def parse_model(self) -> Model:
        kw = self.expect_kw("model")
        name = self.expect("NAME")
        self.expect("{")

        species: list[Species] = []
        reactions: list[Reaction] = []
        params: list[Param] = []
        invariants: list[Invariant] = []
        properties: list[FluxProperty] = []
        steady_state = False

        while not self.at("}"):
            if self.at("EOF"):
                self._err("unexpected end of input: missing '}'")
            if self.at_kw("species"):
                species.append(self.parse_species())
            elif self.at_kw("reaction"):
                reactions.append(self.parse_reaction())
            elif self.at_kw("param"):
                params.append(self.parse_param())
            elif self.at_kw("invariant"):
                invariants.append(self.parse_invariant())
            elif self.at_kw("steady_state"):
                self.advance()
                steady_state = True
            elif self.at_kw("property"):
                properties.append(self.parse_property())
            else:
                self._err(
                    f"expected species/reaction/param/invariant/steady_state/"
                    f"property, found {self._desc(self.cur)}"
                )

        close = self.expect("}")
        return Model(
            name=name.value,
            species=species,
            reactions=reactions,
            params=params,
            invariants=invariants,
            span=self._span(kw, close),
            source=self.src,
            steady_state=steady_state,
            properties=properties,
        )

    def parse_species(self) -> Species:
        kw = self.expect_kw("species")
        name = self.expect("NAME")
        initial = 0.0
        end: Token = name
        if self.at("@"):
            self.advance()
            self.expect_kw("init")
            initial, end = self._number()
        return Species(name=name.value, initial=initial, span=self._span(kw, end),
                       has_init=end is not name)

    def parse_side(self, terminator: str) -> list[SpeciesRef]:
        # An empty side (source `-> A` or sink `A ->`) is allowed: it ends
        # immediately at the terminator token.
        if self.at(terminator):
            return []
        terms = [self.parse_term()]
        while self.at("+"):
            self.advance()
            terms.append(self.parse_term())
        return terms

    def parse_term(self) -> SpeciesRef:
        coeff = 1.0
        start = self.cur
        if self.at("NUMBER"):
            coeff = Num(self.advance().value)
        name = self.expect("NAME")
        return SpeciesRef(
            coeff=coeff, species=name.value, span=self._span(start, name)
        )

    def parse_reaction(self) -> Reaction:
        kw = self.expect_kw("reaction")
        name = self.expect("NAME")
        self.expect(":")
        reactants = self.parse_side("->")
        self.expect("->")
        products = self.parse_side("@")
        self.expect("@")
        law = self.expect("NAME")
        if law.value not in KNOWN_RATE_LAWS:
            raise BSLError(
                f"unknown rate law {law.value!r} (expected one of: "
                f"{', '.join(sorted(KNOWN_RATE_LAWS))})",
                law.line,
                law.col,
            )
        self.expect("(")
        args = [self.parse_rate_arg()]
        while self.at(","):
            self.advance()
            args.append(self.parse_rate_arg())
        close = self.expect(")")
        lo, hi = RATE_LAW_ARITY[law.value]
        if not (lo <= len(args) <= hi):
            want = str(lo) if lo == hi else f"{lo}-{hi}"
            raise BSLError(
                f"rate law {law.value!r} expects {want} argument(s), "
                f"got {len(args)}",
                law.line,
                law.col,
            )
        return Reaction(
            name=name.value,
            reactants=reactants,
            products=products,
            rate_law=law.value,
            rate_args=args,
            span=self._span(kw, close),
        )

    def parse_rate_arg(self) -> RateArg:
        t = self.cur
        if self.at("NUMBER"):
            self.advance()
            return RateArg(name=None, value=Num(t.value), span=self._span(t, t))
        if self.at("NAME"):
            self.advance()
            return RateArg(name=t.value, value=None, span=self._span(t, t))
        self._err(
            f"expected a parameter name or number in rate law, "
            f"found {self._desc(t)}"
        )

    def parse_param(self) -> Param:
        kw = self.expect_kw("param")
        name = self.expect("NAME")
        self.expect_kw("in")
        self.expect("[")
        lo, _ = self._number()
        self.expect(",")
        hi, hi_tok = self._number()
        close = self.expect("]")

        grade = GRADE_ASSUMED
        grade_meta: dict = {}
        end: Token = close
        if self.at("@"):
            self.advance()
            g = self.expect("NAME")
            if g.value == "experiment":
                self.expect("(")
                self.expect_kw("replicates")
                self.expect("=")
                reps, _ = self._number()
                self.expect(",")
                self.expect_kw("p")
                self.expect("=")
                pval, _ = self._number()
                end = self.expect(")")
                grade = GRADE_EXPERIMENT
                grade_meta = {"replicates": int(reps), "p": pval}
            elif g.value == "literature":
                self.expect("(")
                self.expect_kw("citations")
                self.expect("=")
                cites, _ = self._number()
                end = self.expect(")")
                grade = GRADE_LITERATURE
                grade_meta = {"citations": int(cites)}
            elif g.value == "assumed":
                end = g
                grade = GRADE_ASSUMED
            else:
                raise BSLError(
                    f"unknown confidence grade {g.value!r} "
                    f"(expected experiment/literature/assumed)",
                    g.line,
                    g.col,
                )
        return Param(
            name=name.value,
            lo=lo,
            hi=hi,
            grade=grade,
            grade_meta=grade_meta,
            span=self._span(kw, end),
        )

    def parse_invariant(self) -> Invariant:
        kw = self.expect_kw("invariant")
        name = self.expect("NAME")
        self.expect(":")
        terms = self.parse_side("=")
        self.expect("=")
        rhs, end = self._number()
        return Invariant(
            name=name.value, terms=terms, rhs=rhs, span=self._span(kw, end)
        )

    def parse_property(self) -> FluxProperty:
        kw = self.expect_kw("property")
        name = self.expect("NAME")
        self.expect(":")
        self.expect_kw("flux")
        self.expect("(")
        rxn = self.expect("NAME")
        self.expect(")")
        self.expect_kw("in")
        self.expect("[")
        lo, _ = self._number()
        self.expect(",")
        hi, _ = self._number()
        close = self.expect("]")
        return FluxProperty(
            name=name.value, reaction=rxn.value, lo=lo, hi=hi,
            span=self._span(kw, close),
        )


def parse(text: str, name: str = "<string>") -> Model:
    src = Source.from_text(name, text)
    toks = tokenize(text)
    parser = _Parser(toks, src)
    model = parser.parse_model()
    # The source hash covers the whole file, so nothing may follow the model:
    # trailing declarations would be hashed as evidence yet silently ignored.
    if not parser.at("EOF"):
        parser._err(f"unexpected {parser._desc(parser.cur)} after the end of "
                    f"model {model.name!r}")
    return model


def parse_file(path: str | Path) -> Model:
    path = Path(path)
    # Decode the raw bytes: text-mode I/O normalizes CRLF/CR to LF on every
    # platform, so the hash and byte spans would describe different bytes than
    # the file on disk. The source hash is therefore of the exact file bytes;
    # `.gitattributes` keeps `*.bsl` byte-identical across checkouts.
    data = path.read_bytes()
    try:
        text = data.decode("utf-8")
    except UnicodeDecodeError as e:
        line = data[:e.start].count(b"\n") + 1
        col = e.start - (data.rfind(b"\n", 0, e.start) + 1) + 1
        raise BSLError(f"file is not valid UTF-8 (byte 0x{data[e.start]:02x})",
                       line, col) from None
    return parse(text, name=path.name)
