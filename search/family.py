"""Stage 2: what-if map inside the class where the paper's analysis applies unchanged.

A *shape* is an identity of Schönhage's form: s terms (x_i + P_ij)(y_j + Q_ij)(z_ij + z0), one per
outer output, plus one term that feeds only z0. Together they compute an outer product with s entries
and an inner product of length b. Schönhage's family <k,1,n> (+) <1,(k-1)(n-1),1> (the paper uses
k = n = 3) has s = kn and b = (k-1)(n-1). A shape with k != n is used together with its transpose on
equally many levels, so tiles stay square and each level contributes sqrt(s) to N0 on both sides.

A *schedule* splits the L levels into groups. Group j uses shape j on lam_j*m levels, mu_j*m of which
are inner (sum of mu_j = 1). A tile then holds the products X_Q Y_Q for the sets Q with mu_j*m
levels in group j, and the counts of Section 2.4.3 factor over the groups:
  alpha = prod C(m_j, d_j) s_j^d_j,   beta = prod C(L_j, m_j - d_j) s_j^(L_j - m_j + d_j),
where d_j is the number of levels of Q in group j at which a leaf picks a shared term. Lemma 11's
union bound over the classes (d_j) gives the cost M*exp(m*Gamma), with
  Gamma = max_delta min(A, B) = min_t max_delta (t A + (1-t) B)   (A and B are concave),
and the inner maximum separates over the groups. Encodings are pruned (NOTES.md, lever 3), and the
hash prime sits at the fixed point sigma = 1/2 + gamma(sigma)/4 (lever 4).
"""

import math
from typing import NamedTuple

from search.exponents import H, argmax

GOLDEN = (math.sqrt(5) - 1) / 2


class Shape(NamedTuple):
    name: str
    s: int  # outer outputs, one term each
    b: int  # inner product length


def schoenhage(k, n):
    return Shape(f"S({k},{n})", k * n, (k - 1) * (n - 1))


class Group(NamedTuple):
    shape: Shape
    mu: float  # fraction of the m inner levels in this group
    lam: float  # levels of this group, per m


def golden_max(f, lo, hi, iters=40):
    a, b = lo, hi
    for _ in range(iters):
        x1, x2 = b - GOLDEN * (b - a), a + GOLDEN * (b - a)
        if f(x1) < f(x2):
            a = x1
        else:
            b = x2
    return f((a + b) / 2)


def _psi(g, t):
    """max over delta of t*A_g(delta) + (1-t)*B_g(delta) for one group, per m."""
    s, mu, lam = g.shape.s, g.mu, g.lam
    if mu <= 0:
        return 0.0
    ln_s = math.log(s)
    base = lam * H(mu / lam)

    def f(d):
        a = mu * (H(d) + d * ln_s)
        b = lam * H(mu * (1 - d) / lam) - base + mu * d * ln_s
        return t * a + (1 - t) * b

    return golden_max(f, 0.0, 1.0)


def ln_D(schedule):
    return sum(g.mu * math.log(g.shape.b) for g in schedule)


def gamma(schedule, kappa):
    """Saving of the pruned recursion when |W| <= N^2/D^kappa (Lemma 11, exact)."""
    lnd = ln_D(schedule)

    def neg(t):
        return -(-t * kappa * lnd + sum(_psi(g, t) for g in schedule))

    big_gamma = -golden_max(neg, 0.0, 1.0)
    return -big_gamma / lnd


def ln_N_min(schedule, gam):
    """ln of the smallest N allowed, per m: encodings within N^2/D^gamma, and the tile fits."""
    ln_k = sum(g.lam * H(g.mu / g.lam) for g in schedule)
    ln_n0 = sum((g.lam - g.mu) * math.log(g.shape.s) / 2 for g in schedule)
    # pruned encodings: leaves with at most mu_j*m symbols P0 in group j
    ln_e = 0.0
    for g in schedule:
        x = min(g.mu, g.lam / (g.shape.s + 1))
        ln_e += g.lam * H(x / g.lam) + (g.lam - x) * math.log(g.shape.s)
    return max(ln_e - ln_k / 2 - ln_n0 + gam * ln_D(schedule), ln_k / 2 + ln_n0)


def sigma_fixed_point(schedule):
    s = 0.5
    for _ in range(100):
        s, prev = 0.5 + gamma(schedule, s) / 4, s
        if abs(s - prev) < 1e-8:
            break
    return s


def score(schedule, use_sigma=True):
    kappa = sigma_fixed_point(schedule) if use_sigma else 0.5
    gam = gamma(schedule, kappa)
    if gam <= 0:
        return dict(kappa=kappa, gamma=gam, eps=0.0, et=0.0)
    eps = ln_D(schedule) / ln_N_min(schedule, gam)
    return dict(kappa=kappa, gamma=gam, eps=eps, et=gam * eps / 2)


# ---------------------------------------------------------------------------
# Optimization over schedules
# ---------------------------------------------------------------------------

def nelder_mead(f, x0, step=0.5, iters=150, tol=1e-10):
    """Minimize f from x0 (stdlib Nelder-Mead)."""
    n = len(x0)
    pts = [list(x0)] + [[x0[j] + (step if j == i else 0) for j in range(n)] for i in range(n)]
    vals = [f(p) for p in pts]
    for _ in range(iters):
        order = sorted(range(n + 1), key=vals.__getitem__)
        pts, vals = [pts[i] for i in order], [vals[i] for i in order]
        if abs(vals[-1] - vals[0]) < tol:
            break
        cen = [sum(p[j] for p in pts[:-1]) / n for j in range(n)]
        refl = [cen[j] + (cen[j] - pts[-1][j]) for j in range(n)]
        fr = f(refl)
        if fr < vals[0]:
            exp = [cen[j] + 2 * (cen[j] - pts[-1][j]) for j in range(n)]
            fe = f(exp)
            pts[-1], vals[-1] = (exp, fe) if fe < fr else (refl, fr)
        elif fr < vals[-2]:
            pts[-1], vals[-1] = refl, fr
        else:
            con = [cen[j] + 0.5 * (pts[-1][j] - cen[j]) for j in range(n)]
            fc = f(con)
            if fc < vals[-1]:
                pts[-1], vals[-1] = con, fc
            else:
                for i in range(1, n + 1):
                    pts[i] = [pts[0][j] + 0.5 * (pts[i][j] - pts[0][j]) for j in range(n)]
                    vals[i] = f(pts[i])
    i = min(range(n + 1), key=vals.__getitem__)
    return pts[i], vals[i]


def _schedule(shapes, x):
    """Unconstrained parameters -> schedule: softmax weights for mu, exp for c_j - 1."""
    j = len(shapes)
    logits = [0.0] + list(x[: j - 1])
    top = max(logits)
    w = [math.exp(v - top) for v in logits]
    tot = sum(w)
    mus = [v / tot for v in w]
    cs = [1 + math.exp(v) for v in x[j - 1:]]
    return [Group(sh, mu, mu * c) for sh, mu, c in zip(shapes, mus, cs)]


def best_single(shape, use_sigma=True):
    def et(c):
        return score([Group(shape, 1.0, c)], use_sigma)["et"]

    c = argmax(et, 1.05, 4 * (shape.s + 1), steps=60, iters=40)
    return [Group(shape, 1.0, c)], score([Group(shape, 1.0, c)], use_sigma)


def best_mixture(shapes, starts=None, use_sigma=True):
    """Best schedule using the given shapes, started from each single-shape optimum."""
    singles = {sh: best_single(sh, use_sigma)[0][0].lam for sh in shapes}
    starts = starts or [[0.0] * (len(shapes) - 1)]
    best = None
    for logits in starts:
        x0 = list(logits) + [math.log(singles[sh] - 1) for sh in shapes]

        def obj(x):
            try:
                return -score(_schedule(shapes, x), use_sigma)["et"]
            except (ValueError, ZeroDivisionError, OverflowError):
                return 0.0

        x, v = nelder_mead(obj, x0)
        if best is None or v < best[1]:
            best = (x, v)
    sched = _schedule(shapes, best[0])
    return sched, score(sched, use_sigma)


def describe(schedule, sc):
    groups = ", ".join(f"{g.shape.name}: mu={g.mu:.3f} c={g.lam / g.mu if g.mu else float('inf'):.2f}"
                       for g in schedule)
    return (f"[{groups}] kappa={sc['kappa']:.4f} gamma={sc['gamma']:.4f} eps={sc['eps']:.4f} "
            f"ET={sc['et']:.6f} 3SUM={2 - sc['et'] / 2:.6f} APSP(fn10)={3 - sc['et']:.6f}")


FAMILY = [schoenhage(k, n) for k, n in [(3, 3), (2, 3), (2, 4), (2, 5), (3, 4), (2, 6), (3, 5),
                                         (4, 4), (4, 5), (5, 5)]]

GATE = 1.15 * 0.0020953  # Stage-0 best ET saving, plus 15%


def hypothetical(s_values=(5, 6, 7, 8, 9, 10, 12), b_values=(3, 4, 5, 6, 8)):
    """Best ET saving of Schönhage-shaped identities with s outer outputs and inner length b.

    Within this incidence class the pairing bound gives b <= (k-1)(n-1) for s = kn, so every
    entry above the family is unreachable; the table shows what a different sharing structure
    would have to match in effect.
    """
    out = {}
    for s in s_values:
        for b in b_values:
            out[(s, b)] = best_single(Shape(f"H({s},{b})", s, b))[1]["et"]
    return out


def main():
    print("Single shapes from Schönhage's family (pruned encodings, hash prime at its fixed point):")
    singles = {}
    for sh in FAMILY:
        sched, sc = best_single(sh)
        singles[sh] = sc["et"]
        print("  " + describe(sched, sc))

    print("\nMixtures of S(3,3) with one other family member:")
    base = FAMILY[0]
    for sh in FAMILY[1:]:
        sched, sc = best_mixture([base, sh], starts=[[-3.0], [0.0], [3.0]])
        gain = sc["et"] / singles[base] - 1
        print(f"  {gain:+7.2%}  " + describe(sched, sc))

    print(f"\nHypothetical Schönhage-shaped identities (ET saving; * = passes the gate {GATE:.6f}):")
    table = hypothetical()
    bs = sorted({b for _, b in table})
    print("   s\\b " + "".join(f"{b:>11d}" for b in bs))
    for s in sorted({s for s, _ in table}):
        cells = "".join(f"{table[(s, b)]:10.6f}{'*' if table[(s, b)] >= GATE else ' '}" for b in bs)
        print(f"  {s:4d} {cells}")


if __name__ == "__main__":
    main()
