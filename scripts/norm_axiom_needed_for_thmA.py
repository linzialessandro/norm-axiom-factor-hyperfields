"""(V3) is needed in Theorem A (Remark on where the norm axiom is used).

H = F_5/{+-1} = {0, [1], [2]} with the trivial valuation satisfies (V0)-(V2),
but T = {1, 4} != {1} = 1 + m_rho for the (necessarily trivial) valuation on F_5,
and (V3) fails because 1 - 1 = {0, [2]} contains an element of value 0.
"""
from itertools import product

p, T = 5, (1, 4)
cls = lambda x: 0 if x % p == 0 else min((x * t) % p for t in T)
H = sorted({cls(x) for x in range(p)})
add = lambda a, b: {a} if b == 0 else {b} if a == 0 else {cls(a + b * t) for t in T}
mul = lambda a, b: cls(a * b)
val = lambda x: float('inf') if x == 0 else 0
assert H == [0, 1, 2]
for x, y in product(H, H):
    assert (val(x) == float('inf')) == (x == 0)                       # V0
    assert val(mul(x, y)) == val(x) + val(y)                           # V1
    S = add(x, y)
    assert all(val(z) >= min(val(x), val(y)) for z in S)               # V2
    if 0 not in S:
        assert len({val(z) for z in S}) == 1                           # single-value property (not needed)
neg = {x: next(y for y in H if 0 in add(x, y)) for x in H}
assert add(1, neg[1]) == {0, 2} and val(2) == 0                        # V3 fails (Lemma 2.4)
assert set(T) != {1}                                                   # T != 1 + m_rho = {1}
print("OK: F_5/{+-1}, trivial valuation: (V0)-(V2) hold, (V3) fails, T != 1+m_rho")
