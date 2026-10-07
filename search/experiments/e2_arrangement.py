"""E2: does the arrangement of rows and columns change how many leaves the pruned recursion visits?

One tile of the recursion of Section 2.3 (Schönhage's identity, L levels, m inner levels, K0 x K0
block products), one band of N = K0 * 3^(L-m) rows and one of N columns. A wanted set W of density
1/p comes from weights w(a, b) mod p (W = {w = 0}), for several weight structures:
  random     w uniform
  separable  w = f(a) + g(b)        (W is a union of p bicliques)
  hankel     w = F(a + b)            (W is a union of anti-diagonals)
Each wanted position (I, J) is the output string with the inner set Q of its block product and the
outer strings of I and J (Section 2.4.4). The number of visited leaves is the size of the union of
the 10^m leaves of these output strings (Lemma 10), counted exactly.

Usage: python3 -m search.experiments.e2_arrangement [L m p trials]
"""

import itertools
import math
import random
import sys


def tile(L, m):
    k0 = math.isqrt(math.comb(L, m))
    subsets = list(itertools.combinations(range(L), m))[: k0 * k0]
    return k0, subsets


def leaf_count(L, m, wanted, subsets, k0, n0):
    """|Leaves(U)| for the wanted positions of one tile (rows, cols in [k0*n0])."""
    offsets = {}
    seen = set()
    for i, j in wanted:
        bi, ri = divmod(i, n0)
        bj, rj = divmod(j, n0)
        q = subsets[bi * k0 + bj]
        if q not in offsets:
            offsets[q] = [sum(d * 10 ** (L - 1 - lv) for d, lv in zip(ds, q))
                          for ds in itertools.product(range(10), repeat=m)]
        base, outer = 0, [lv for lv in range(L) if lv not in q]
        for lv in reversed(outer):
            ri, x = divmod(ri, 3)
            rj, y = divmod(rj, 3)
            base += (3 * x + y) * 10 ** (L - 1 - lv)
        for off in offsets[q]:
            seen.add(base + off)
    return len(seen)


def weights(kind, n, p, rng):
    if kind == "random":
        table = [[rng.randrange(p) for _ in range(n)] for _ in range(n)]
        return lambda a, b: table[a][b]
    if kind == "separable":
        f = [rng.randrange(p) for _ in range(n)]
        g = [rng.randrange(p) for _ in range(n)]
        return lambda a, b: (f[a] + g[b]) % p
    if kind == "hankel":
        big_f = [rng.randrange(p) for _ in range(2 * n)]
        return lambda a, b: big_f[a + b]
    raise ValueError(kind)


def run(L=6, m=2, p=4, trials=3, seed=1):
    rng = random.Random(seed)
    k0, subsets = tile(L, m)
    n0 = 3 ** (L - m)
    n = k0 * n0
    total = 10 ** L
    print(f"L={L} m={m} K0={k0} N0={n0} n={n} p={p}: all 10^L = {total} leaves, "
          f"{len(subsets) * n0 * n0} output strings")
    for kind in ("random", "separable", "hankel"):
        for arrangement in ("identity", "shuffled", "sorted"):
            counts = []
            for _ in range(trials):
                w = weights(kind, n, p, rng)
                rows, cols = list(range(n)), list(range(n))
                if arrangement == "shuffled":
                    rng.shuffle(rows)
                    rng.shuffle(cols)
                elif arrangement == "sorted" and kind == "separable":
                    # rows with equal f, and columns with equal g, become contiguous
                    rows.sort(key=lambda a: w(a, 0))
                    cols.sort(key=lambda b: w(0, b))
                wanted = [(i, j) for i in range(n) for j in range(n) if w(rows[i], cols[j]) == 0]
                counts.append((len(wanted), leaf_count(L, m, wanted, subsets, k0, n0)))
            if arrangement == "sorted" and kind != "separable":
                continue
            u = sum(c[0] for c in counts) / trials
            v = sum(c[1] for c in counts) / trials
            print(f"  {kind:9s} {arrangement:8s} |U|={u:9.0f}  leaves={v:9.0f}  "
                  f"leaves/|U|={v / u:6.2f}  leaves/10^L={v / total:.3f}")


if __name__ == "__main__":
    run(*map(int, sys.argv[1:]))
