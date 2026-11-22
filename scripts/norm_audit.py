"""The norm is intrinsic, and which half of Theorem A uses which half of (V3).

(1) In H_rho(Q_p), rho = {0, ..., n-1}, the set val(1 (-) 1) \\ {inf} is {n, n+1, ...}
    on a window, so Gamma_{>=0} \\ val(1 (-) 1) = rho (Remark 2.6).
(2) H = H_{{0,1}}(Q_3) with the norm {0}: 1 (-) 1 is contained in m_{0}, so Step 2 of
    Theorem A goes through, but 3 lies in m_{0} and not in 1 (-) 1, 1 (+) 3 != {1},
    and T = 1 + 9Z_3 is strictly smaller than 1 + m_{0} = 1 + 3Z_3: Step 3 fails.
(3) F_5/{+-1} with the trivial valuation: m_rho = {0} is contained in 1 (-) 1, so
    Step 3 holds, but 1 (-) 1 = {0, [2]} is not contained in m_rho: Step 2 fails.
"""
def padic(p, n, W):
    """Elements of value 0..W as (k, a mod p^(k+n)) with p^k || a."""
    els = [(k, a) for k in range(W + 1) for a in range(p ** (k + n)) if a % p ** k == 0 and (a // p ** k) % p]
    N = W + 2 * n + 2
    S = range(1, p ** N, p ** n)  # representatives of 1+m^n mod p^N (enough, see below)
    def cls(c):
        if c % p ** N == 0:
            return None
        k = 0
        while c % p ** (k + 1) == 0:
            k += 1
        return (k, c % p ** (k + n))
    def hsum(x, y):
        out = set()
        for s in S:
            c = cls(x[1] + y[1] * s)
            out.add(c)
        return out
    return els, hsum, (lambda x: x[1] % p ** n), p ** n


W = 3
for p, n in [(2, 2), (3, 2), (3, 3), (5, 2)]:
    els, hsum, _, _ = padic(p, n, W)
    one, minus_one = (0, 1), (0, (-1) % p ** n)
    omo = hsum(one, minus_one)
    vals = {x[0] for x in omo if x is not None and x[0] < W + n}
    assert None in omo and vals == set(range(n, W + n)), (p, n, sorted(vals))
    rho = sorted(set(range(W + n)) - vals)
    assert rho == list(range(n)), (p, n, rho)
print("OK (1): Gamma_{>=0} \\ val(1 (-) 1) = rho in H_rho(Q_p) on the window")

p, n = 3, 2
els, hsum, _, _ = padic(p, n, W)
omo = hsum((0, 1), (0, p ** n - 1))
assert all(x is None or x[0] >= 1 for x in omo)          # 1 (-) 1 inside m_{0}: Step 2 ok
three = (1, 3)
assert three not in omo                                   # m_{0} not inside 1 (-) 1
assert hsum((0, 1), three) != {(0, 1)}                    # Lemma 2.5 fails at norm {0}
assert (0, 4) in hsum((0, 1), three)                      # 1 + 3 = 4 is not in T = 1 + 9Z_3
print("OK (2): H_{0,1}(Q_3) with norm {0}: Step 2 holds, Step 3 fails")

T = (1, 4)
cls = lambda a: 0 if a % 5 == 0 else min(a * t % 5 for t in T)
omo = {cls(1 - t) for t in T}
assert omo == {0, 2}                                      # {0} in 1 (-) 1, and [2] has value 0
print("OK (3): F_5/{+-1}, trivial valuation: Step 3 holds, Step 2 fails")
