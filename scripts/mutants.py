"""Mutation test for layering.py: the checks must reject broken constructions.

Mutant 1 forgets the tail B_gamma when an equal-value sum cancels.
Mutant 2 uses the wrong comparison in the absorption rule of add_el_set.
Each mutant must produce at least one violation for M = Massouros (Z/2)^2.
"""
from pathlib import Path
from massouros import massouros

SRC = Path(__file__).with_name("layering.py").read_text()
MUTATIONS = [
    ("g if 0 in S else None", "None"),
    ("if x == ZERO or x[1] > u:", "if x == ZERO or x[1] >= u:"),
]

for old, new in MUTATIONS:
    assert old in SRC, old
    code = SRC.replace(old, new).replace('if __name__ == "__main__":', "if False:")
    ns = {"__name__": "mutant"}
    exec(compile(code, "layering_mutant", "exec"), ns)
    try:
        ns["check"](massouros(2), f"mutant [{old} -> {new}]", True)
    except AssertionError:
        print(f"killed: {old!r} -> {new!r}")
        continue
    raise SystemExit(f"SURVIVED: {old!r} -> {new!r}")
print("OK: all mutants killed")
