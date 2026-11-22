"""Massouros hyperfields M(G) = G u {0}, G an elementary abelian 2-group.

x + y = {x, y} for distinct nonzero x, y;  x + x = M \\ {x};  x + 0 = {x}.
Checks: (1) M(G) is a hyperfield for |G| = 2, 4, 8 (Massouros 1985, Prop. 2);
(2) for |G| = 2 it IS a factor hyperfield, namely F_5 / {1, -1}, so the
non-quotient theorem needs |G| >= 4, as in our Lemma on Massouros
hyperfields.
"""
from hyper import check_hyperfield


def massouros(k):
    n = 2 ** k  # nonzero elements are bit vectors 0..n-1, shifted by +1
    elems = list(range(n + 1))  # 0 = zero, element i>0 encodes vector i-1
    def mul(x, y):
        if x == 0 or y == 0:
            return 0
        return ((x - 1) ^ (y - 1)) + 1
    def add(x, y):
        if x == 0:
            return frozenset({y})
        if y == 0:
            return frozenset({x})
        if x != y:
            return frozenset({x, y})
        return frozenset(e for e in elems if e != x)
    return elems, add, mul


def factor_hyperfield_prime(p, T):
    """F_p / T for a subgroup T of F_p^x; returns elems, add, mul, cls."""
    cosets, cls = [], {0: 0}
    for a in range(1, p):
        if a not in cls:
            c = frozenset(a * t % p for t in T)
            cosets.append(c)
            for b in c:
                cls[b] = len(cosets)
    elems = list(range(len(cosets) + 1))
    rep = {0: 0}
    for i, c in enumerate(cosets, 1):
        rep[i] = min(c)
    def add(x, y):
        return frozenset(cls[(rep[x] + rep[y] * t) % p] for t in T)
    def mul(x, y):
        return cls[rep[x] * rep[y] % p]
    return elems, add, mul, cls


if __name__ == "__main__":
    for k in (1, 2, 3):
        errs = check_hyperfield(*massouros(k))
        print(f"M((Z/2)^{k}): {len(errs)} axiom violations")
        assert not errs
    # |G| = 2: compare with F_5/{1,4}
    elems, add, mul, cls = factor_hyperfield_prime(5, [1, 4])
    assert not check_hyperfield(elems, add, mul)
    me, madd, mmul = massouros(1)
    # the only candidate bijection: 0->0, 1->1, other->other
    iso = {0: 0, 1: 1, 2: 2}
    same = all(frozenset(iso[z] for z in add(x, y)) == madd(iso[x], iso[y])
               for x in elems for y in elems)
    print("F_5/{1,-1} isomorphic to M(Z/2):", same)
    assert same
    print("OK")
