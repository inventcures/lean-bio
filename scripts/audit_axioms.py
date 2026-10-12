"""Fail unless every listed theorem depends only on Lean's standard axioms.

`grep sorry` is not an axiom audit: `axiom cheat : False`, `native_decide`
(`Lean.ofReduceBool`) or a stray `sorryAx` from a macro all pass it. This runs
`#print axioms` in the Lake project and checks the answer.

    python scripts/audit_axioms.py lean BslLean THEOREM [THEOREM ...]
"""

from __future__ import annotations

import re
import subprocess
import sys
import tempfile
from pathlib import Path

STANDARD = {"propext", "Classical.choice", "Quot.sound"}


def main(argv: list[str]) -> int:
    project, module, *theorems = argv
    src = f"import {module}\n" + "".join(f"#print axioms {t}\n" for t in theorems)
    with tempfile.TemporaryDirectory() as td:
        f = Path(td) / "Audit.lean"
        f.write_text(src, encoding="utf-8")
        proc = subprocess.run(["lake", "env", "lean", str(f)], cwd=project,
                              capture_output=True, text=True)
    out = proc.stdout + proc.stderr
    print(out)
    if proc.returncode != 0:
        return 1
    reports = re.findall(r"'([^']+)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)",
                         out, re.S)
    if len(reports) != len(theorems):
        print(f"expected {len(theorems)} axiom reports, got {len(reports)}")
        return 1
    bad = False
    for name, axioms in reports:
        extra = {a.strip() for a in axioms.split(",") if a.strip()} - STANDARD
        if extra:
            print(f"NON-STANDARD AXIOMS in {name}: {sorted(extra)}")
            bad = True
    return 1 if bad else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
