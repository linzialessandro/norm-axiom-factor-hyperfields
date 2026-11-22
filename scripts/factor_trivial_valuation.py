"""Sanity check of the factor-hyperfield rigidity theorem in the smallest case.

For a finite field F_p (whose only valuation is trivial, value group 0,
norm {0}), the factor hyperfield F_p/T carries a Krasner valuation exactly
when T = 1 + m_{0} = {1}.  Norm axiom with Gamma = 0: for z in x + y, z' lies
in x + y iff every w in z - z' has value > 0, i.e. w = 0.
"""
from massouros import factor_hyperfield_prime


def krasner_trivial_ok(elems, add, neg):
    for x in elems:
        for y in elems:
            S = add(x, y)
            for z in S:
                for z2 in elems:
                    ball = all(w == 0 for w in add(z, neg[z2]))
                    if (z2 in S) != ball:
                        return False
    return True


for p in [2, 3, 5, 7, 11, 13, 17, 19, 23]:
    g = next(g for g in range(1, p) if len({pow(g, k, p) for k in range(p - 1)}) == p - 1) if p > 2 else 1
    for d in [d for d in range(1, p) if (p - 1) % d == 0]:
        T = sorted({pow(g, k * ((p - 1) // d), p) for k in range(d)})
        elems, add, mul, cls = factor_hyperfield_prime(p, T)
        neg = {x: next(y for y in elems if 0 in add(x, y)) for x in elems}
        ok = krasner_trivial_ok(elems, add, neg)
        assert ok == (T == [1]), (p, T)
print("OK: F_p/T admits the trivial Krasner valuation iff T = {1}")
