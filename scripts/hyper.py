"""Small finite hyperfields and an axiom checker.

A finite hyperfield is given by its elements 0..n-1 (0 is the zero, 1 the
unit), a multiplication table on nonzero elements, and a function add(x, y)
returning a frozenset.  check_hyperfield verifies every axiom of
Linzi--Touchard, Definitions 1.1 and 1.4, by brute force.
"""
from itertools import product


def check_hyperfield(elems, add, mul, zero=0, one=1):
    E = list(elems)
    errors = []

    def setadd(A, B):
        out = set()
        for a in A:
            for b in B:
                out |= add(a, b)
        return frozenset(out)

    for x, y in product(E, E):
        if not add(x, y):
            errors.append(("empty sum", x, y))
        if add(x, y) != add(y, x):
            errors.append(("CH2", x, y))
    for x, y, z in product(E, E, E):
        if setadd(add(x, y), {z}) != setadd({x}, add(y, z)):
            errors.append(("CH1", x, y, z))
    neg = {}
    for x in E:
        inv = [y for y in E if zero in add(x, y)]
        if len(inv) != 1:
            errors.append(("CH3", x, inv))
        else:
            neg[x] = inv[0]
    if errors:
        return errors
    for x, y, z in product(E, E, E):
        if z in add(x, y) and x not in add(z, neg[y]):
            errors.append(("CH4", x, y, z))
    for x in E:
        if mul(x, zero) != zero:
            errors.append(("absorb", x))
    nz = [x for x in E if x != zero]
    for x in nz:
        if mul(x, one) != x or not any(mul(x, y) == one for y in nz):
            errors.append(("group", x))
        for y in nz:
            if mul(x, y) != mul(y, x) or mul(x, y) == zero:
                errors.append(("group", x, y))
            for z in nz:
                if mul(mul(x, y), z) != mul(x, mul(y, z)):
                    errors.append(("assoc mul", x, y, z))
    for x, y, z in product(E, E, E):
        if frozenset(mul(x, w) for w in add(y, z)) != add(mul(x, y), mul(x, z)):
            errors.append(("HF3", x, y, z))
    return errors
