"""Brute-force check of the transfer theorem: k_S x| Gamma = K_T.

K is the Laurent series field over k = F_p, truncated at relative precision P,
with Gamma = Z, and T = {u : v(u) = 0, lc(u) in S}.  The map
Phi([x]_T) = [lc x]_S t^{v(x)} should be an isomorphism K_T -> k_S x| Z.  For
x, y with values in a window and every s in T mod t^P, we compute the set
{Phi(x + y s)}, and compare it with the layered sum [lc x] t^a (+) [lc y] t^b
of Definition 6.2, both truncated to values < min(a, b) + P.  'DEEP' stands
for 0 together with every element of value >= min(a, b) + P.

It also checks the table rows, with Gamma = Z truncated:
  Krasner x| Z  = Viro's tropical hyperfield Y on Z (gamma -> -gamma),
  sign x| Z     = Viro's tropical real hyperfield TR on +-2^{-gamma},
  and that 1 lies in 1 (-) 1 for both, so neither admits a Krasner valuation.
"""
from itertools import product

DEEP = "DEEP"


def check_transfer(p, S, P=3, window=(0, 1, 2), mutant=False):
    S = frozenset(S)
    cls = lambda a: min((a * l) % p for l in S)          # class of a in k_S
    Mnz = sorted({cls(a) for a in range(1, p)})

    def Madd(a, b):                                       # [a]_S (+) [b]_S, a, b != 0
        return {0 if (a + b * l) % p == 0 else cls(a + b * l) for l in S}

    units = [u for u in product(range(p), repeat=P) if u[0] != 0]
    T = [u for u in units if u[0] in S]
    if mutant:                                            # wrong T: also force u_1 = 0
        T = [u for u in T if u[1] == 0]

    def mul(u, s):                                        # product of units mod t^P
        return tuple(sum(u[i] * s[j - i] for i in range(j + 1)) % p for j in range(P))

    def phi_sum(a, u, b, w):
        mu = min(a, b)
        out = set()
        for s in T:
            ws = mul(w, s)
            z = [0] * P                                   # coefficients of t^mu .. t^{mu+P-1}
            for i in range(P):
                if a + i - mu < P:
                    z[a + i - mu] += u[i]
                if b + i - mu < P:
                    z[b + i - mu] += ws[i]
            z = [c % p for c in z]
            nz = [i for i in range(P) if z[i]]
            out.add((cls(z[nz[0]]), mu + nz[0]) if nz else DEEP)
        return out

    def layer_sum(c, a, d, b):
        mu = min(a, b)
        if a < b:
            return {(c, a)}
        if b < a:
            return {(d, b)}
        A = Madd(c, d)
        out = {(e, a) for e in A if e != 0}
        if 0 in A:
            out |= {(e, g) for e in Mnz for g in range(a + 1, a + P)} | {DEEP}
        return out

    n = 0
    for a, b in product(window, window):
        for u, w in product(units, units):
            got = phi_sum(a, u, b, w)
            exp = layer_sum(cls(u[0]), a, cls(w[0]), b)
            assert got == exp, (p, S, a, u, b, w, got, exp)
            n += 1
    # The T-orbits on units, computed by multiplying out, are exactly the fibres
    # of u -> [lc u]_S, so Phi is well defined and injective on classes of value 0.
    for u in units:
        orbit = {mul(u, s) for s in T}
        assert orbit == {w for w in units if cls(w[0]) == cls(u[0])}, (p, S, u)
    return n


cases = [(5, {1}, "F_5 (field row)"), (3, {1, 2}, "Krasner as F_3/F_3^x"),
         (5, {1, 2, 3, 4}, "Krasner as F_5/F_5^x"), (5, {1, 4}, "M(Z/2) = F_5/{+-1}"),
         (7, {1, 2, 4}, "F_7/squares"), (7, {1, 6}, "F_7/{+-1}")]
for p, S, name in cases:
    n = check_transfer(p, S, P=3 if p < 7 else 2)
    print(f"OK transfer {name}: {n} pairs, K_T = k_S x| Z on the window")
try:
    check_transfer(5, {1, 4}, P=3, mutant=True)
    raise SystemExit("mutant T was not rejected")
except AssertionError:
    print("OK mutant T = {lc in S, u_1 = 0} is rejected")


# --- table rows: Krasner x| Z vs Viro's Y, sign x| Z vs Viro's TR (truncated) ---
W = range(-3, 4)


def lay(Madd, Mnz, x, y, lo=-3, hi=3):
    """layered sum, truncated: elements (c, g) with g <= hi; None marks 0."""
    if x is None:
        return {y}
    if y is None:
        return {x}
    (c, a), (d, b) = x, y
    if a != b:
        return {x if a < b else y}
    A = Madd(c, d)
    out = {(e, a) for e in A if e != 0}
    if 0 in A:
        out |= {(e, g) for e in Mnz for g in range(a + 1, hi + 1)} | {None}
    return out


# Krasner K = {0, 1}: 1 (+) 1 = {0, 1}
Kadd = lambda c, d: {0, 1}
Y = lambda g: None if g is None else -g                  # (1, g) -> -g in Y; None -> -inf
for a, b in product(list(W) + [None], repeat=2):
    x = None if a is None else (1, a)
    y = None if b is None else (1, b)
    got = {Y(None if z is None else z[1]) for z in lay(Kadd, [1], x, y)}
    A, B = Y(a), Y(b)
    if A is None:
        exp = {B}
    elif B is None:
        exp = {A}
    elif A != B:
        exp = {max(A, B)}
    else:
        exp = {c for c in range(-3, A + 1)} | {None}      # {c in Y : c <= A}, truncated at -3
    assert got == exp, (a, b, got, exp)
print("OK Krasner x| Z = Viro's tropical hyperfield Y (truncated)")

# sign S = {0, 1, -1}: 1 (+) 1 = {1}, 1 (+) -1 = {0, 1, -1}
Sadd = lambda c, d: {c} if c == d else {0, 1, -1}
from fractions import Fraction as Fr
R = lambda z: 0 if z is None else z[0] * Fr(2) ** (-z[1])
pts = [None] + [(e, g) for e in (1, -1) for g in W]
for x, y in product(pts, repeat=2):
    got = {R(z) for z in lay(Sadd, [1, -1], x, y)}
    a, b = R(x), R(y)
    if abs(a) > abs(b):
        exp = {a}
    elif abs(a) < abs(b):
        exp = {b}
    elif a == b:
        exp = {a}
    else:                                                 # a = -b: [-|a|, |a|], truncated
        exp = {R(z) for z in pts if abs(R(z)) <= abs(a)}
    assert got == exp, (x, y, got, exp)
print("OK sign x| Z = Viro's tropical real hyperfield TR (truncated)")

# 1 in 1 (-) 1 in both, so no valuation of any norm (Lemma 2.4 would give val(1) > 0)
assert (1, 0) in lay(Kadd, [1], (1, 0), (1, 0))
assert (1, 0) in lay(Sadd, [1, -1], (1, 0), (-1, 0))
print("OK 1 in 1 (-) 1 in Krasner x| Z and sign x| Z")
