"""Brute-force check of the layered hyperfield L = M x| Z.

Elements: ZERO, or (a, g) with a a nonzero element of the finite hyperfield M
and g in Z.  Sums of two elements of equal value g whose M-sum contains 0 are
infinite; we encode a set as (explicit finite set, tail), where tail = u means
"0 together with every element of value > u".  Because only the relative order
of values matters, testing values in {0,1,2} covers every order pattern for
associativity; reversibility samples tail elements up to value 5.

Checks, for M in {Massouros (Z/2)^1, (Z/2)^2, F_3, Krasner K, sign S}:
  hyperfield axioms (CH1)-(CH4), (HF3) on the test window, and the valuation
  axioms (V0)-(V2); also checks the single-value property (not needed); and that the norm axiom (V3) fails for each tested M that is not a field (the Massouros, Krasner and sign hyperfields).
"""
from itertools import product
from hyper import check_hyperfield
from massouros import massouros

ZERO = "0"


def make(M):
    Melems, Madd, Mmul = M
    Mnz = [a for a in Melems if a != 0]
    Mneg = {a: next(b for b in Melems if 0 in Madd(a, b)) for a in Melems}

    def val(x):
        return None if x == ZERO else x[1]

    def norm(E, u):
        if u is None:
            return (frozenset(E), None)
        return (frozenset(e for e in E if e != ZERO and e[1] <= u), u)

    def add_el(x, y):
        if x == ZERO:
            return norm({y}, None)
        if y == ZERO:
            return norm({x}, None)
        (a, g), (b, h) = x, y
        if g < h:
            return norm({x}, None)
        if h < g:
            return norm({y}, None)
        S = Madd(a, b)
        return norm({(c, g) for c in S if c != 0}, g if 0 in S else None)

    def union(sets):
        E, u = set(), None
        for (E2, u2) in sets:
            E |= E2
            if u2 is not None:
                u = u2 if u is None else min(u, u2)
        return norm(E, u)

    def add_el_set(x, A):
        E, u = A
        parts = [add_el(x, e) for e in E]
        if u is not None:
            if x == ZERO or x[1] > u:
                parts.append(norm(set(), u))
            else:
                parts.append(norm({x}, None))
        return union(parts)

    def member(e, A):
        E, u = A
        return e in E or (u is not None and (e == ZERO or e[1] > u))

    def neg(x):
        return ZERO if x == ZERO else (Mneg[x[0]], x[1])

    def mul(x, y):
        if x == ZERO or y == ZERO:
            return ZERO
        return (Mmul(x[0], y[0]), x[1] + y[1])

    def scale(c, A):
        E, u = A
        return norm({mul(c, e) for e in E}, None if u is None else u + c[1])

    def sample(A, top):
        E, u = A
        out = set(E)
        if u is not None:
            out.add(ZERO)
            out |= {(a, g) for a in Mnz for g in range(u + 1, top + 1)}
        return out

    return dict(val=val, add_el=add_el, add_el_set=add_el_set, member=member,
                neg=neg, mul=mul, scale=scale, sample=sample, Mnz=Mnz)


def check(M, name, expect_v3_fail):
    L = make(M)
    window = [ZERO] + [(a, g) for a in L["Mnz"] for g in (0, 1, 2)]
    bad = 0
    for x, y, z in product(window, repeat=3):
        left = L["add_el_set"](z, L["add_el"](x, y))
        right = L["add_el_set"](x, L["add_el"](y, z))
        bad += left != right
    # add_el_set must agree with the elementwise union over a sampled tail
    def cut(A, top):
        return frozenset(e for e in L["sample"](A, top) if e == ZERO or e[1] <= top)
    for x, y, z in product(window, repeat=3):
        A = L["add_el"](y, z)
        fast = cut(L["add_el_set"](x, A), 4)
        slow = frozenset()
        for w in L["sample"](A, 6):
            slow |= cut(L["add_el"](x, w), 4)
        bad += fast != slow
    for x, y in product(window, repeat=2):
        bad += L["add_el"](x, y) != L["add_el"](y, x)
        bad += L["member"](ZERO, L["add_el"](x, y)) != (y == L["neg"](x))
        for z in L["sample"](L["add_el"](x, y), 5):
            bad += not L["member"](x, L["add_el"](z, L["neg"](y)))
        for c in [(a, g) for a in L["Mnz"] for g in (-1, 0, 1)]:
            bad += L["scale"](c, L["add_el"](x, y)) != L["add_el"](L["mul"](c, x), L["mul"](c, y))
        # valuation axiom (V2); single-value property (not needed)
        S = L["add_el"](x, y)
        vals = [L["val"](e) for e in L["sample"](S, 5) if e != ZERO]
        mins = [L["val"](e) for e in (x, y) if e != ZERO]
        if mins:
            bad += any(v < min(mins) for v in vals)
        if not L["member"](ZERO, S):
            bad += len(set(vals)) != 1
    one = (1, 0)
    S = L["add_el"](one, L["neg"](one))
    v3_fails = any(e != ZERO and e[1] <= 0 for e in L["sample"](S, 3))
    print(f"{name}: violations={bad}, (V3) fails on 1-1: {v3_fails}")
    assert bad == 0 and v3_fails == expect_v3_fail


if __name__ == "__main__":
    def field3():
        elems = [0, 1, 2]
        return elems, (lambda x, y: frozenset({(x + y) % 3})), (lambda x, y: x * y % 3)
    def krasner():
        return [0, 1], (lambda x, y: frozenset({0, 1}) if x == y == 1 else frozenset({x + y})), (lambda x, y: x * y)
    def sign():
        enc = {0: 0, 1: 1, 2: -1}; dec = {0: 0, 1: 1, -1: 2}
        def add(x, y):
            a, b = enc[x], enc[y]
            if a == 0: return frozenset({y})
            if b == 0: return frozenset({x})
            if a == b: return frozenset({x})
            return frozenset({0, 1, 2})
        return [0, 1, 2], add, (lambda x, y: dec[enc[x] * enc[y]])
    for M, name, f in [(massouros(1), "Massouros (Z/2)^1", True),
                       (massouros(2), "Massouros (Z/2)^2", True),
                       (field3(), "F_3", False),
                       (krasner(), "Krasner K", True),
                       (sign(), "sign S", True)]:
        assert not check_hyperfield(*M)
        check(M, name, f)
    print("OK")
