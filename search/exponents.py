"""Exponent calculus for the thin-product theorem of Alman and Vassilevska Williams,
"Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided
Graphs" (arXiv 2610.06783), together with the cheap baseline levers of the
identity-search plan (see NOTES.md).

Conventions follow the paper: Schönhage's identity has 10 terms, an outer 3x3
product and an inner product of length 4, so D = 4^m, N0 = 3^(L-m), L = c*m.
A thin-product saving gamma at thinness D <= N^eps turns into an Exact Triangle
saving gamma*eps/2 (Theorem 17, Remark 20), which 3SUM keeps half of and APSP a
third of (Theorem 21, 22), or all of via footnote 10.

All logarithms are natural. Standard library only.
"""

import math

LN2, LN3, LN4, LN9, LN10 = (math.log(x) for x in (2, 3, 4, 9, 10))


def H(x):
    """Entropy function with natural logarithms."""
    if x <= 0 or x >= 1:
        return 0.0
    return -x * math.log(x) - (1 - x) * math.log1p(-x)


def lncomb(n, k):
    return math.lgamma(n + 1) - math.lgamma(k + 1) - math.lgamma(n - k + 1)


def logsumexp(xs):
    top = max(xs)
    return top + math.log(sum(math.exp(x - top) for x in xs))


def bisect(f, lo, hi, iters=100):
    """Root of f on [lo, hi], given f(lo) < 0 < f(hi)."""
    for _ in range(iters):
        mid = (lo + hi) / 2
        if f(mid) < 0:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def argmax(f, lo, hi, steps=200, iters=80):
    """Maximize f on [lo, hi]: a grid search, then golden-section refinement."""
    h = (hi - lo) / steps
    best = max(range(steps + 1), key=lambda i: f(lo + i * h))
    a, b = max(lo, lo + (best - 1) * h), min(hi, lo + (best + 1) * h)
    g = (math.sqrt(5) - 1) / 2
    for _ in range(iters):
        x1, x2 = b - g * (b - a), a + g * (b - a)
        if f(x1) < f(x2):
            a = x1
        else:
            b = x2
    return (a + b) / 2


# ---------------------------------------------------------------------------
# Section 4.4: the data structure (Theorem 30, Corollaries 31 and 32)
# ---------------------------------------------------------------------------

def rho(c):
    """Decay rate rho_c = 9/(c-1) of the beta_d (Corollary 31)."""
    return 9 / (c - 1)


def box_gamma(c, theta):
    """Preprocessing saving gamma of Corollary 31."""
    return theta * math.log(1 / rho(c)) / LN4


def query_exp(theta):
    """Query exponent q of Corollary 31."""
    return (H(theta) + theta * LN9) / LN4


def R(c, gamma):
    """Thinness bound R_c(gamma) of (11): encodings of all 10^L leaves."""
    return LN4 / (c * LN10 - c * H(1 / c) / 2 - (c - 1) * LN3 + gamma * LN4)


def R_pruned(c, gamma):
    """Thinness bound when only the leaves with at most m symbols P0 are encoded.

    The encodings of a band then cost about M = K*N0^2 (see pruned_yates_profile),
    so the condition (10) becomes N >= sqrt(K)*N0*D^gamma.
    """
    return LN4 / (c * H(1 / c) / 2 + (c - 1) * LN3 + gamma * LN4)


def eps_star():
    """Upper limit ln4/(5 ln10) of the technique (Corollary 31)."""
    return LN4 / (5 * LN10)


def theta_for_query(q):
    """The theta in (0, 0.9) at which query_exp(theta) = q."""
    return bisect(lambda t: query_exp(t) - q, 1e-12, 0.9)


def cor32_gamma(c, kappa):
    """Saving of Corollary 32 at the theta that balances gamma = kappa - q."""
    theta = bisect(lambda t: box_gamma(c, t) - (kappa - query_exp(t)), 1e-12, 0.9)
    return box_gamma(c, theta)


# ---------------------------------------------------------------------------
# Section 2.4.3: the pruned recursion with W known in advance (Lemma 11)
# ---------------------------------------------------------------------------

def maxmin_gamma(c, kappa):
    """Saving of the first inequality of Lemma 11, taken exactly.

    Per m, a tile with |U| = M/D^kappa wanted entries visits at most
    max over delta of min(f1, g2) leaves of order delta*m, relative to M, where
    f1 = ln(|U| alpha_d / M)/m increases on [0, 0.9] and g2 = ln(beta_d / M)/m
    decreases for c > 10, so the maximum is at their crossing.
    """
    def f1(d):
        return -kappa * LN4 + H(d) + d * LN9

    def g2(d):
        return c * H((1 - d) / c) - c * H(1 / c) + d * LN9

    d = bisect(lambda d: f1(d) - g2(d), 0.0, 0.9)
    return -g2(d) / LN4


def lemma11_finite_gamma(c, kappa, m):
    """The saving given by the sum of Lemma 11 at a finite m, with L = round(c*m)."""
    L = round(c * m)
    ln_M = lncomb(L, m) + (L - m) * LN9
    ln_U = ln_M - kappa * m * LN4
    terms = [min(ln_U + lncomb(m, d) + d * LN9, lncomb(L, m - d) + (L - m + d) * LN9)
             for d in range(m + 1)]
    return (ln_M - logsumexp(terms)) / (m * LN4)


def pruned_yates_profile(c, m):
    """Sizes of the stages of Yates' algorithm restricted to the needed entries.

    Stage k holds the entries (tau_1..tau_k, u_{k+1}..u_L) with at most m symbols
    P0 in the prefix of terms and at most m inner variables in the suffix of left
    variables; all other entries are either unneeded or zero. Returns the list of
    ln(stage size) - ln(M) for k = 0..L.
    """
    L = round(c * m)
    ln_M = lncomb(L, m) + (L - m) * LN9
    out = []
    for k in range(L + 1):
        ln_pre = logsumexp([lncomb(k, j) + (k - j) * LN9 for j in range(min(m, k) + 1)])
        ln_suf = logsumexp([lncomb(L - k, i) + i * LN4 + (L - k - i) * LN3
                            for i in range(min(m, L - k) + 1)])
        out.append(ln_pre + ln_suf - ln_M)
    return out


# ---------------------------------------------------------------------------
# Section 3: from the thin-product saving to Exact Triangle, 3SUM, and APSP
# ---------------------------------------------------------------------------

def et_saving(gamma, eps):
    """Exact Triangle saving: n^3 D^(-gamma/2) with D = n^eps (Remark 20)."""
    return gamma * eps / 2


def three_sum(et):
    """3SUM exponent through Exact Triangle (Theorem 21(a), 22)."""
    return 2 - et / 2


def apsp(et):
    """APSP exponent through Exact Triangle detection (Theorem 21(b), 22)."""
    return 3 - et / 3


def apsp_all_edges(et):
    """APSP exponent through all-edges Exact Triangle (footnote 10)."""
    return 3 - et


def three_sum_kpp16(gamma, eps):
    """3SUM exponent through the randomized reduction of [KPP16], which by
    footnote 10 keeps all of the saving gamma*eps of the thin-product theorem
    (claimed in the paper, not re-derived here)."""
    return 2 - gamma * eps


def sigma_fixed_point(gamma_of_kappa):
    """Hash-prime exponent sigma, with p = D^sigma in Theorem 17.

    With pieces of D^(1-sigma)/g vertices, the instances cost n^3 g D^(2 sigma-1-gamma)
    and the scans n^3 D^(1-2 sigma)/g. Balancing gives n^3 D^(-gamma/2) as long as
    g = D^(1-2 sigma+gamma/2) >= 1, where gamma is the saving at kappa = sigma, so the
    best choice is the fixed point sigma = 1/2 + gamma(sigma)/4.
    """
    s = 0.5
    for _ in range(100):
        s, prev = 0.5 + gamma_of_kappa(s) / 4, s
        if abs(s - prev) < 1e-13:
            break
    return s


# ---------------------------------------------------------------------------
# Baselines
# ---------------------------------------------------------------------------

def _row(name, c, kappa, gamma, eps):
    et = et_saving(gamma, eps)
    return dict(name=name, c=c, kappa=kappa, gamma=gamma, eps=eps, et=et,
                three_sum=three_sum(et), apsp=apsp(et), apsp_all_edges=apsp_all_edges(et),
                three_sum_kpp16=three_sum_kpp16(gamma, eps))


def _best_c(gamma_of_c, eps_of_c_gamma, lo=10.05, hi=60.0):
    def score(c):
        g = gamma_of_c(c)
        return g * eps_of_c_gamma(c, g)

    c = argmax(score, lo, hi)
    g = gamma_of_c(c)
    return c, g, eps_of_c_gamma(c, g)


def baselines():
    """The levers of the plan, each row adding one to the one it names."""
    rows = [
        _row("Thm 5 as stated (gamma = eps = 1/18)", 19, 0.5, 1 / 18, 1 / 18),
        _row("Cor 26 as stated (gamma = 0.063, eps = 1/18)", 21, 0.5, 0.063, 1 / 18),
    ]

    g = cor32_gamma(21, 0.5)
    rows.append(_row("rounding slack: c = 21, eps = R_21(gamma)", 21, 0.5, g, R(21, g)))

    c, g, e = _best_c(lambda c: cor32_gamma(c, 0.5), R)
    rows.append(_row("Cor 32, best c", c, 0.5, g, e))

    c, g, e = _best_c(lambda c: maxmin_gamma(c, 0.5), R)
    rows.append(_row("exact Lemma 11 (max-min), best c", c, 0.5, g, e))

    c, g, e = _best_c(lambda c: maxmin_gamma(c, 0.5), R_pruned)
    rows.append(_row("  + pruned encodings", c, 0.5, g, e))

    def sigma_route(eps_fn):
        def gamma_of_c(c):
            return maxmin_gamma(c, sigma_fixed_point(lambda k: maxmin_gamma(c, k)))
        c, g, e = _best_c(gamma_of_c, eps_fn)
        return c, sigma_fixed_point(lambda k: maxmin_gamma(c, k)), g, e

    c, s, g, e = sigma_route(R)
    rows.append(_row("  + hash prime p = D^sigma", c, s, g, e))
    c, s, g, e = sigma_route(R_pruned)
    rows.append(_row("  + pruned encodings + hash prime", c, s, g, e))
    return rows


def main():
    print(f"eps* = {eps_star():.6f}")
    print(f"{'lever':48s} {'c':>6s} {'kappa':>6s} {'gamma':>7s} {'eps':>7s} {'ET':>8s} "
          f"{'3SUM':>9s} {'APSP':>9s} {'APSP fn10':>9s} {'3SUM rnd':>9s}")
    for r in baselines():
        print(f"{r['name']:48s} {r['c']:6.2f} {r['kappa']:6.4f} {r['gamma']:7.4f} {r['eps']:7.4f} "
              f"{r['et']:8.6f} {r['three_sum']:9.6f} {r['apsp']:9.6f} {r['apsp_all_edges']:9.6f} "
              f"{r['three_sum_kpp16']:9.6f}")


if __name__ == "__main__":
    main()
