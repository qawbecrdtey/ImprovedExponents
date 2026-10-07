"""Generator of the Lean certificates for the global bounds on the saving.

The function is S(c) = F(A(c), Gam(c)) for c > 10, where A is the thinness constant of the
encoding (basePruned for pruned encodings, baseFull for the paper's encodings), Gam is the common
value of gammaX(c, .) and gammaQ at their crossing, and F(A, g) = g ln 4 / (2 (A + g ln 4)) (see
ImprovedExponents/Optimum/Defs.lean). A is nondecreasing and Gam is nondecreasing, so on a cell
[c1, c2] we have S(c) <= F(A(c1), Gam(c2)). For each encoding this module cuts (10, C_MAX] into
cells on which that bound is below U_OUT (outside the window of the maximum) or below U_IN
(inside the window), and writes the Lean files

    ImprovedExponents/Optimum/GlobalCells1.lean ... GlobalCellsK.lean   (one lemma per cell)
    ImprovedExponents/Optimum/GlobalCells.lean                          (the three ranges)

for pruned encodings (window [21, 23], bounds 0.002095 and 0.002096), and

    ImprovedExponents/Optimum/GlobalFullCells1.lean ... GlobalFullCellsK.lean
    ImprovedExponents/Optimum/GlobalFullCells.lean

for the paper's encodings (window [20.8, 22], bounds 0.002059 and 0.002061), and

    ImprovedExponents/Optimum/Shapes/Cells_S{k}{n}_1.lean ...     (one lemma per cell)
    ImprovedExponents/Optimum/Shapes/Cells_S{k}{n}.lean           (ranges, tail, witness)

for the nine other shapes (k, n) of Schönhage's family (s = kn outer outputs, inner length
b = (k-1)(n-1); `shapeSaving s b c` of ImprovedExponents/Optimum/Shapes/Defs.lean, for c > s+1),
with the window around the maximum chosen automatically and the bounds at +-1e-6 of the maximum
rounded to six digits; the join file also has the tail [c_max, oo) and a lower-bound witness.

Each cell is proved by the toolkit of Optimum/NumLog.lean from three rational inequalities:
Alo <= A(c1), gammaX(c2, theta) <= ghi and gammaQ(theta) <= ghi at a theta near the crossing.
The functions `log_lo`, `log_hi`, `gamma_x_hi`, `gamma_q_hi`, `base_pruned_lo` and
`base_full_lo` below evaluate the toolkit's rational enclosures exactly (with
`fractions.Fraction`), so that every number written to a Lean file has been checked here by the
very inequality that Lean will check. Floating point (search/exponents.py) only guides the choice
of the cells and of theta.

Usage:

    python3 -m search.certs                      # write the Lean files of both encodings
    python3 -m search.certs --check              # compare with the files on disk, write nothing
    python3 -m search.certs --stats              # print the cells, write nothing
    python3 -m search.certs --encoding full ...  # one encoding only (`pruned`, `full`, `shapes`
                                                 # or one shape such as `S24`)

Standard library only.
"""

import argparse
import math
import os
import re
import sys
from fractions import Fraction as Fr

from search.exponents import H, LN3, LN4, LN9, LN10, argmax, bisect

# Upstream's rational bounds on ln 2, ln 3 and ln 10 (ThreeSumApsp/Sec4/Table2/LogBounds.lean).
LOG2_LO, LOG2_HI = Fr("0.6931471803"), Fr("0.6931471808")
LOG3_LO, LOG3_HI = Fr("1.0986122881"), Fr("1.0986122892")
LOG10_LO, LOG10_HI = Fr("2.3025850922"), Fr("2.3025850938")
TERMS = 4

C_MIN = Fr(10)
MAX_CELLS_PER_FILE = 60

LEAN_DIR = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                        "ImprovedExponents", "Optimum")


# ---------------------------------------------------------------------------
# The toolkit's enclosures, in exact rational arithmetic
# ---------------------------------------------------------------------------

def series_arg(k, x):
    """Upstream's `seriesArg k x`."""
    p = Fr(2) ** k
    return (x - p) / (x + p)


def log_lo(k, x):
    """The toolkit's `logLo k x`, a lower bound on ln x."""
    return _log_approx(k, x) - _log_err(k, x)


def log_hi(k, x):
    """The toolkit's `logHi k x`, an upper bound on ln x."""
    return _log_approx(k, x) + _log_err(k, x)


def _log_approx(k, x):
    s = series_arg(k, x)
    return k * (LOG2_LO + LOG2_HI) / 2 + 2 * sum(s ** (2 * i + 1) / (2 * i + 1)
                                                for i in range(TERMS))


def _log_err(k, x):
    s = series_arg(k, x)
    return abs(k) * (LOG2_HI - LOG2_LO) / 2 + 2 * (s ** (2 * TERMS) / (1 - s ** 2))


def nearest_k(x):
    """The integer k for which 2^k is nearest to x > 0 (it minimizes |seriesArg k x|)."""
    k0 = math.floor(math.log2(float(x)))
    return min((k0 - 1, k0, k0 + 1), key=lambda k: (abs(series_arg(k, x)), k))


def gamma_x_hi(k, c, theta):
    """The least r that `gammaX_le k : gammaX c theta <= r` accepts."""
    g2_lo = (-(c - 1) * log_hi(0, (c - 1 + theta) / (c - 1)) - theta * log_hi(k, c - 1 + theta)
             - (1 - theta) * log_hi(0, 1 - theta) + theta * (2 * LOG3_LO))
    return -g2_lo / (2 * LOG2_LO)


def gamma_q_hi(k, theta):
    """The least r that `gammaQ_le k : gammaQ theta <= r` accepts."""
    rhs = (-theta * log_hi(k, theta) - (1 - theta) * log_hi(0, 1 - theta)
           + theta * (2 * LOG3_LO))
    return (2 - 4 * rhs / (2 * LOG2_HI)) / 3


def c_ent_lo(k, c):
    """The toolkit's `cEntLo k c`, a lower bound on c H(1/c)."""
    return (c - 1) * log_lo(0, c / (c - 1)) + log_lo(k, c)


def c_ent_hi(k, c):
    """The toolkit's `cEntHi k c`, an upper bound on c H(1/c)."""
    return (c - 1) * log_hi(0, c / (c - 1)) + log_hi(k, c)


def base_pruned_lo(k, c):
    """The largest r that `le_basePruned k : r <= basePruned c` accepts."""
    return c_ent_lo(k, c) / 2 + (c - 1) * LOG3_LO


def base_full_lo(k, c):
    """The largest r that `le_baseFull k : r <= baseFull c` accepts."""
    return c * LOG10_LO - c_ent_hi(k, c) / 2 - (c - 1) * LOG3_HI


def saving_ok(alo, ghi, u):
    """The last hypothesis of `savingF_lt`: F(alo, ghi) < u."""
    return 0 < alo and 0 <= u <= Fr(1, 2) and ghi * (1 - 2 * u) * (2 * LOG2_HI) < 2 * u * alo


def g2_s_lo(kx, ks, s, c, theta):
    """The toolkit's `g2SLo kx ks s c theta`, a lower bound on g2S s c theta."""
    return (-(c - 1) * log_hi(0, (c - 1 + theta) / (c - 1)) - theta * log_hi(kx, c - 1 + theta)
            - (1 - theta) * log_hi(0, 1 - theta) + theta * log_lo(ks, s))


def g2_s_hi(kx, ks, s, c, theta):
    """The toolkit's `g2SHi kx ks s c theta`, an upper bound on g2S s c theta."""
    return (-(c - 1) * log_lo(0, (c - 1 + theta) / (c - 1)) - theta * log_lo(kx, c - 1 + theta)
            - (1 - theta) * log_lo(0, 1 - theta) + theta * log_hi(ks, s))


def gamma_x_s_hi(kx, ks, kb, s, b, c, theta):
    """The least r that `gammaXS_le kx ks kb : gammaXS s b c theta <= r` accepts."""
    return -g2_s_lo(kx, ks, s, c, theta) / log_lo(kb, b)


def gamma_x_s_lo(kx, ks, kb, s, b, c, theta):
    """The largest r that `le_gammaXS kx ks kb : r <= gammaXS s b c theta` accepts."""
    return -g2_s_hi(kx, ks, s, c, theta) / log_hi(kb, b)


def gamma_q_s_hi(k, ks, kb, s, b, theta):
    """The least r that `gammaQS_le k ks kb : gammaQS s b theta <= r` accepts."""
    rhs = (-theta * log_hi(k, theta) - (1 - theta) * log_hi(0, 1 - theta)
           + theta * log_lo(ks, s))
    return (2 - 4 * rhs / log_hi(kb, b)) / 3


def gamma_q_s_lo(k, ks, kb, s, b, theta):
    """The largest r that `le_gammaQS k ks kb : r <= gammaQS s b theta` accepts."""
    lhs = (-theta * log_lo(k, theta) - (1 - theta) * log_lo(0, 1 - theta)
           + theta * log_hi(ks, s))
    return (2 - 4 * lhs / log_lo(kb, b)) / 3


def base_s_lo(k, ks, s, c):
    """The largest r that `le_basePrunedS k ks : r <= basePrunedS s c` accepts."""
    return c_ent_lo(k, c) / 2 + (c - 1) * log_lo(ks, s) / 2


def base_s_hi(k, ks, s, c):
    """The least r that `basePrunedS_le k ks : basePrunedS s c <= r` accepts."""
    return c_ent_hi(k, c) / 2 + (c - 1) * log_hi(ks, s) / 2


def saving_s_ok(kb, b, alo, ghi, u):
    """The last hypothesis of `savingS_lt kb`: savingS b alo ghi < u."""
    return 0 < alo and 0 <= u <= Fr(1, 2) and ghi * (1 - 2 * u) * log_hi(kb, b) < 2 * u * alo


def round_down(x, digits):
    return Fr(math.floor(x * 10 ** digits), 10 ** digits)


def round_up(x, digits):
    return Fr(math.ceil(x * 10 ** digits), 10 ** digits)


# ---------------------------------------------------------------------------
# Floating-point reference
# ---------------------------------------------------------------------------

def gamma_q(theta):
    return (2 - 4 * (H(theta) + theta * LN9) / LN4) / 3


def gamma_x(c, theta):
    return -(c * H((1 - theta) / c) - c * H(1 / c) + theta * LN9) / LN4


def theta_star(c):
    """The crossing of gammaX(c, .) and gammaQ in (0, 0.9)."""
    return bisect(lambda t: gamma_x(c, t) - gamma_q(t), 1e-9, 0.9, iters=60)


def gam(c):
    return gamma_x(c, theta_star(c))


def base_pruned(c):
    return c / 2 * H(1 / c) + (c - 1) * LN3


def base_full(c):
    return c * LN10 - c / 2 * H(1 / c) - (c - 1) * LN3


# ---------------------------------------------------------------------------
# The two encodings
# ---------------------------------------------------------------------------

class Encoding:
    """The data of one encoding: its thinness constant (exactly and in floating point), the Lean
    names, the window of the maximum, the certified numerals and the names of the files."""

    kind = "encoding"
    fn_text = "F(A(c), Γ(c))"
    s, b, ln_b = 9, 4, LN4
    c_min, theta_max = C_MIN, Fr(9, 10)
    import_line = "public import ImprovedExponents.Optimum.GlobalLemmas"

    def __init__(self, name, base, base_lo, base_float, mono, le_base, win_lo, win_hi, c_max,
                 u_out, u_in, prefix, lemma, doc):
        self.name, self.base, self.base_lo, self.base_float = name, base, base_lo, base_float
        self.mono, self.le_base = mono, le_base
        self.win_lo, self.win_hi, self.c_max = win_lo, win_hi, c_max
        self.u_out, self.u_in = u_out, u_in
        self.prefix, self.lemma, self.doc = prefix, lemma, doc
        self.join_name = prefix
        self.module_dir = "ImprovedExponents.Optimum."
        self.statement = f"savingF ({base} c) (Gam c)"

    def saving(self, c):
        """S(c) in floating point."""
        g = gam(c)
        return LN4 * g / (2 * (self.base_float(c) + g * LN4))

    def theta_star(self, c):
        return theta_star(c)

    def gam(self, c):
        return gam(c)

    def gamma_x_hi(self, kx, c, theta):
        return gamma_x_hi(kx, c, theta)

    def gamma_q_hi(self, kq, theta):
        return gamma_q_hi(kq, theta)

    def saving_ok(self, alo, ghi, u):
        return saving_ok(alo, ghi, u)

    def bound_for(self, c):
        """u_in inside the window, u_out elsewhere (for the cell starting at c)."""
        return self.u_in if self.win_lo <= c < self.win_hi else self.u_out


PRUNED = Encoding("pruned", "basePruned", base_pruned_lo, base_pruned, "basePruned_monotoneOn",
                  "le_basePruned", Fr(21), Fr(23), Fr(200), Fr("0.002095"), Fr("0.002096"),
                  "GlobalCells", "savingF_pruned", "pruned encodings")
FULL = Encoding("full", "baseFull", base_full_lo, base_full, "baseFull_monotoneOn",
                "le_baseFull", Fr("20.8"), Fr(22), Fr(200), Fr("0.002059"), Fr("0.002061"),
                "GlobalFullCells", "savingF_full", "the paper's encodings")


class Shape(Encoding):
    """A shape (k, n) of Schönhage's family: s = kn outer outputs, inner length b = (k-1)(n-1).
    The window of the maximum, the certified numerals and c_max are computed from the
    floating-point maximum `sup` of `shapeSaving s b`: the bounds are `round(sup, 6) ± margin`."""

    kind = "shape"
    import_line = "public import ImprovedExponents.Optimum.Shapes.NumLog"

    def __init__(self, k, n, margin=Fr(1, 10 ** 6)):
        self.k, self.n, self.s, self.b = k, n, k * n, (k - 1) * (n - 1)
        self.ln_s, self.ln_b = math.log(self.s), math.log(self.b)
        self.k_s, self.k_b = nearest_k(Fr(self.s)), nearest_k(Fr(self.b))
        self.c_min, self.theta_max = Fr(self.s + 1), Fr(self.s, self.s + 1)
        self.margin = margin
        s, b = self.s, self.b
        self.name, self.base, self.mono, self.le_base = f"S{k}{n}", f"basePrunedS {s}", "", ""
        self.base_lo = lambda kc, c: base_s_lo(kc, self.k_s, s, c)
        self.base_float = lambda c: c / 2 * H(1 / c) + (c - 1) * self.ln_s / 2
        self.prefix, self.join_name = f"Shapes/Cells_{self.name}_", f"Shapes/Cells_{self.name}"
        self.module_dir = "ImprovedExponents.Optimum.Shapes."
        self.lemma, self.doc = f"shapeSaving_{self.name}", f"the shape `({k}, {n})`"
        self.statement = self.fn_text = f"shapeSaving {s} {b} c"
        # The maximum and the window.
        self.c_star = argmax(self.saving, s + 1.5, 4 * (s + 1), steps=200, iters=60)
        self.sup = self.saving(self.c_star)
        table = Fr(round(self.sup, 6)).limit_denominator(10 ** 6)
        self.u_out, self.u_in = table - margin, table + margin
        u = float(self.u_out)
        root_lo = bisect(lambda x: self.saving(x) - u, s + 1.001, self.c_star)
        root_hi = bisect(lambda x: u - self.saving(x), self.c_star, 10 * (s + 1))
        # The window ends on the grid of tenths, where S is at least 5e-8 below u_out (the cells
        # next to the window would otherwise be narrower than the enclosures allow).
        self.win_lo = round_down(Fr(root_lo), 1)
        while self.saving(float(self.win_lo)) > u - 5e-8:
            self.win_lo -= Fr(1, 10)
        self.win_hi = round_up(Fr(root_hi), 1)
        while self.saving(float(self.win_hi)) > u - 5e-8:
            self.win_hi += Fr(1, 10)
        self.c_max = next(Fr(m) for m in range(100, 5000, 100)
                          if m > self.win_hi and self.saving_ok(
                              BaseBound(Fr(m), self).alo, Fr(2, 3), self.u_out))
        self.witness = Witness(self)

    def gamma_q(self, theta):
        return (2 - 4 * (H(theta) + theta * self.ln_s) / self.ln_b) / 3

    def gamma_x(self, c, theta):
        return -(c * H((1 - theta) / c) - c * H(1 / c) + theta * self.ln_s) / self.ln_b

    def theta_star(self, c):
        return bisect(lambda t: self.gamma_x(c, t) - self.gamma_q(t), 1e-9,
                      float(self.theta_max) - 1e-12, iters=60)

    def gam(self, c):
        return self.gamma_x(c, self.theta_star(c))

    def saving(self, c):
        g = self.gam(c)
        return self.ln_b * g / (2 * (self.base_float(c) + g * self.ln_b))

    def gamma_x_hi(self, kx, c, theta):
        return gamma_x_s_hi(kx, self.k_s, self.k_b, self.s, self.b, c, theta)

    def gamma_q_hi(self, kq, theta):
        return gamma_q_s_hi(kq, self.k_s, self.k_b, self.s, self.b, theta)

    def saving_ok(self, alo, ghi, u):
        return saving_s_ok(self.k_b, self.b, alo, ghi, u)


class Witness:
    """A rational c0 near the maximum of a shape with `u_out < shapeSaving s b c0`, from
    `basePrunedS_le k ks : A(c0) <= ahi` and `le_GamS (le_gammaXS ..) (le_gammaQS ..) :
    glo <= Gam c0` (the hypotheses of `lt_savingS kb`)."""

    def __init__(self, enc):
        self.enc, s, b = enc, enc.s, enc.b
        self.c = round_down(Fr(enc.c_star), 1)
        self.k, self.k_x = nearest_k(self.c), nearest_k(self.c - 1)
        self.ahi = round_up(base_s_hi(self.k, enc.k_s, s, self.c), 5)
        t0 = round_down(Fr(enc.theta_star(float(self.c))), 6)
        best = None
        for j in (-1, 0, 1, 2):
            theta = t0 + Fr(j, 10 ** 6)
            k_q = nearest_k(theta)
            value = min(gamma_x_s_lo(self.k_x, enc.k_s, enc.k_b, s, b, self.c, theta),
                        gamma_q_s_lo(k_q, enc.k_s, enc.k_b, s, b, theta))
            if best is None or value > best[0]:
                best = (value, theta, k_q)
        self.theta, self.k_q = best[1], best[2]
        self.glo = round_down(best[0], 7)

    def valid(self):
        enc, s, b = self.enc, self.enc.s, self.enc.b
        return (enc.c_min < self.c and 0 < self.theta < enc.theta_max
                and 0 <= self.glo <= Fr(2, 3)
                and base_s_hi(self.k, enc.k_s, s, self.c) <= self.ahi
                and self.glo <= gamma_x_s_lo(self.k_x, enc.k_s, enc.k_b, s, b, self.c, self.theta)
                and self.glo <= gamma_q_s_lo(self.k_q, enc.k_s, enc.k_b, s, b, self.theta)
                and 2 * enc.u_out * self.ahi
                < self.glo * (1 - 2 * enc.u_out) * log_lo(enc.k_b, b))


SHAPE_LIST = [(2, 4), (3, 4), (2, 5), (2, 3), (2, 6), (3, 5), (4, 4), (4, 5), (5, 5)]
ENCODINGS = {enc.name: enc for enc in (PRUNED, FULL)}
_SHAPES = {}


def shape(k, n):
    """The shape (k, n), built on first use (its constructor runs the floating-point search)."""
    if (k, n) not in _SHAPES:
        _SHAPES[(k, n)] = Shape(k, n)
    return _SHAPES[(k, n)]


def shapes():
    return [shape(k, n) for k, n in SHAPE_LIST]

# The constants of the pruned encoding, kept as module-level names.
WIN_LO, WIN_HI, C_MAX = PRUNED.win_lo, PRUNED.win_hi, PRUNED.c_max
U_OUT, U_IN = PRUNED.u_out, PRUNED.u_in
STATEMENT = PRUNED.statement


def saving(c, enc=PRUNED):
    return enc.saving(c)


def bound_for(c, enc=PRUNED):
    return enc.bound_for(c)


# ---------------------------------------------------------------------------
# The cells
# ---------------------------------------------------------------------------

class GamBound:
    """A certified bound `Gam c <= ghi`, from theta and the integers of the two enclosures."""

    def __init__(self, c, enc=PRUNED):
        self.c, self.enc = c, enc
        self.k_x = nearest_k(c - 1)
        t0 = round_down(Fr(enc.theta_star(float(c))), 6)
        best = None
        for j in (-1, 0, 1, 2):
            theta = t0 + Fr(j, 10 ** 6)
            k_q = nearest_k(theta)
            value = max(enc.gamma_x_hi(self.k_x, c, theta), enc.gamma_q_hi(k_q, theta))
            if best is None or value < best[0]:
                best = (value, theta, k_q)
        self.theta, self.k_q = best[1], best[2]
        self.ghi = round_up(best[0], 7)

    def valid(self):
        enc = self.enc
        return (enc.c_min < self.c and 0 < self.theta < enc.theta_max
                and 0 <= self.ghi <= Fr(2, 3)
                and enc.gamma_x_hi(self.k_x, self.c, self.theta) <= self.ghi
                and enc.gamma_q_hi(self.k_q, self.theta) <= self.ghi)


class BaseBound:
    """A certified bound `alo <= A(c)` for the thinness constant `A` of the encoding."""

    def __init__(self, c, enc=PRUNED):
        self.c, self.enc = c, enc
        self.k = nearest_k(c)
        self.alo = round_down(enc.base_lo(self.k, c), 5)

    def valid(self):
        return 1 < self.c and self.alo <= self.enc.base_lo(self.k, self.c)


class Cell:
    """The cell [c1, c2] (or (10, c2] if c1 = 10) with the bound u."""

    def __init__(self, base, gam_bound, u):
        self.base, self.gam, self.u = base, gam_bound, u
        self.c1, self.c2 = base.c, gam_bound.c

    def valid(self):
        enc = self.base.enc
        return (enc.c_min <= self.c1 < self.c2 and self.base.valid() and self.gam.valid()
                and self.gam.enc is enc and enc.saving_ok(self.base.alo, self.gam.ghi, self.u))


def next_cell(c1, enc=PRUNED):
    """The cell starting at c1: the largest admissible c2 on a decimal grid."""
    base, u = BaseBound(c1, enc), enc.bound_for(c1)
    limit = min(stop for stop in (enc.win_lo, enc.win_hi, enc.c_max) if stop > c1)

    def cell(c2):
        return Cell(base, GamBound(c2, enc), u)

    whole = cell(limit)
    if whole.valid():
        return whole
    # Floating point: the c at which F(alo, Gam(c)) reaches u.
    g_max = 2 * float(u) * float(base.alo) / ((1 - 2 * float(u)) * enc.ln_b)
    c_star = bisect(lambda x: enc.gam(x) - g_max, float(c1), float(limit), iters=40)
    width = max(c_star - float(c1), 1e-5)
    grid = Fr(10) ** (math.floor(math.log10(width)) - 1)
    c2 = min(Fr(math.floor(Fr(c_star) / grid)) * grid, limit - grid)
    while grid >= Fr(1, 10 ** 6):
        while c2 > c1:
            candidate = cell(c2)
            if candidate.valid():
                return candidate
            c2 -= grid
        grid /= 10
        c2 = c1 + 9 * grid
    raise ValueError(f"no cell starts at {c1}")


def make_cells(enc=PRUNED):
    """The cells from C_MIN to c_max, in order."""
    cells, c = [], enc.c_min
    while c < enc.c_max:
        cells.append(next_cell(c, enc))
        c = cells[-1].c2
    return cells


def tail_base(enc=PRUNED):
    """The bound `alo <= A(c_max)` of the tail [c_max, oo), where Gam < 2/3."""
    return BaseBound(enc.c_max, enc)


# ---------------------------------------------------------------------------
# Lean text
# ---------------------------------------------------------------------------

def dec(x):
    """A rational with a power of ten as denominator, as a Lean decimal numeral."""
    x = Fr(x)
    if x.denominator == 1:
        return str(x.numerator)
    digits = 0
    while (x * 10 ** digits).denominator != 1:
        digits += 1
        if digits > 30:
            raise ValueError(f"{x} is not a decimal")
    n = (x * 10 ** digits).numerator
    sign, n = ("-" if n < 0 else ""), abs(n)
    return f"{sign}{n // 10 ** digits}.{n % 10 ** digits:0{digits}d}"


def lean_int(k):
    return str(k) if k >= 0 else f"({k})"


def interval(cell):
    kind = "Ioc" if cell.c1 == cell.base.enc.c_min else "Icc"
    return f"{kind} ({dec(cell.c1)} : ℝ) {dec(cell.c2)}"


def cell_lemma(index, cell, enc=PRUNED):
    first = cell.c1 == enc.c_min
    left = "(" if first else "["
    b, g = cell.base, cell.gam
    head = [
        f"/-- `{enc.fn_text} < {dec(cell.u)}` for `c ∈ {left}{dec(cell.c1)}, {dec(cell.c2)}]`. -/",
        f"theorem {enc.lemma}_cell_{index} : ∀ c ∈ {interval(cell)},",
        f"    {enc.statement} < {dec(cell.u)} := fun _ hc =>",
    ]
    if enc.kind == "shape":
        lemma = "shapeSaving_lt_of_mem_Ioc" if first else "shapeSaving_lt_of_mem_Icc"
        ks, kb = lean_int(enc.k_s), lean_int(enc.k_b)
        return "\n".join(head + [
            f"  {lemma} {kb}",
            f"    (le_basePrunedS {lean_int(b.k)} {ks} : ({dec(b.alo)} : ℝ) ≤ {enc.base}"
            f" {dec(b.c)})",
            f"    (GamS_le (θ := {dec(g.theta)}) (gammaXS_le {lean_int(g.k_x)} {ks} {kb})",
            f"      (gammaQS_le {lean_int(g.k_q)} {ks} {kb}) :"
            f" GamS {enc.s} {enc.b} {dec(g.c)} ≤ {dec(g.ghi)}) hc",
        ])
    lemma = "savingF_lt_of_mem_Ioc" if first else "savingF_lt_of_mem_Icc"
    return "\n".join(head + [
        f"  {lemma} {enc.mono}",
        f"    ({enc.le_base} {lean_int(b.k)} : ({dec(b.alo)} : ℝ) ≤ {enc.base} {dec(b.c)})",
        f"    (Gam_le (θ := {dec(g.theta)}) (gammaX_le {lean_int(g.k_x)})"
        f" (gammaQ_le {lean_int(g.k_q)}) :",
        f"      Gam {dec(g.c)} ≤ {dec(g.ghi)}) hc",
    ])


def tail_lemma(enc):
    """The tail `[c_max, oo)` of a shape, by `shapeSaving_lt_of_le`."""
    tail = tail_base(enc)
    return "\n".join([
        f"/-- The tail: `{enc.fn_text} < {dec(enc.u_out)}` for `c ≥ {dec(enc.c_max)}`, because"
        f" `Γ(c) < 2/3`. -/",
        f"theorem {enc.lemma}_lt_tail {{c : ℝ}} (hc : {dec(enc.c_max)} ≤ c) :",
        f"    {enc.statement} < {dec(enc.u_out)} :=",
        f"  shapeSaving_lt_of_le {lean_int(enc.k_b)} (le_basePrunedS {lean_int(tail.k)}"
        f" {lean_int(enc.k_s)} :",
        f"    ({dec(tail.alo)} : ℝ) ≤ {enc.base} {dec(enc.c_max)}) hc",
    ])


def witness_lemma(enc):
    """The lower bound `u_out < shapeSaving s b c0` of a shape, by `lt_savingS`."""
    w, ks, kb = enc.witness, lean_int(enc.k_s), lean_int(enc.k_b)
    return "\n".join([
        f"/-- The witness: `{dec(enc.u_out)} < {enc.fn_text}` at `c = {dec(w.c)}`. -/",
        f"theorem {enc.lemma}_witness : ({dec(enc.u_out)} : ℝ) < shapeSaving {enc.s} {enc.b}"
        f" {dec(w.c)} :=",
        f"  lt_savingS {kb} (basePrunedS_pos (by norm_num) (by norm_num))",
        f"    (basePrunedS_le {lean_int(w.k)} {ks} : {enc.base} {dec(w.c)} ≤ {dec(w.ahi)})",
        f"    (le_GamS (θ := {dec(w.theta)}) (le_gammaXS {lean_int(w.k_x)} {ks} {kb})",
        f"      (le_gammaQS {lean_int(w.k_q)} {ks} {kb}) :"
        f" ({dec(w.glo)} : ℝ) ≤ GamS {enc.s} {enc.b} {dec(w.c)})",
    ])


def chain_lemma(name, doc, kind, lo, hi, u, parts, enc=PRUNED):
    """The lemma `name` on `kind lo hi`, joining the lemmas `parts` on adjacent intervals."""
    join = f"forall_mem_{kind}_of_forall_mem_Icc"
    head = [f"/-- {doc} -/",
            f"theorem {name} : ∀ c ∈ {kind} ({dec(lo)} : ℝ) {dec(hi)},"]
    if len(parts) == 1:
        return "\n".join(head + [f"    {enc.statement} < {dec(u)} :=", f"  {parts[0]}"])
    lines = head + [f"    {enc.statement} < {dec(u)} := by", f"  have h := {parts[0]}"]
    lines += [f"  replace h := {join} h {part}" for part in parts[1:]]
    return "\n".join(lines + ["  exact h"])


def split_files(cells, enc=PRUNED):
    """Lists of (index, cell): the three ranges, each cut into files of about equal size."""
    numbered = list(enumerate(cells, start=1))
    files = []
    for lo, hi in ((enc.c_min, enc.win_lo), (enc.win_lo, enc.win_hi), (enc.win_hi, enc.c_max)):
        part = [(i, cell) for i, cell in numbered if lo <= cell.c1 < hi]
        count = -(-len(part) // MAX_CELLS_PER_FILE)
        for j in range(count):
            files.append(part[len(part) * j // count:len(part) * (j + 1) // count])
    return files


def range_text(kind, lo, hi):
    return f"`{'(' if kind == 'Ioc' else '['}{dec(lo)}, {dec(hi)}]`"


def render(cells, enc=PRUNED):
    """The generated Lean files: a dictionary from file names to their contents."""
    out, blocks = {}, []
    for number, part in enumerate(split_files(cells, enc), start=1):
        lo, hi, u = part[0][1].c1, part[-1][1].c2, part[0][1].u
        kind = "Ioc" if lo == enc.c_min else "Icc"
        name = f"{enc.lemma}_block_{number}"
        blocks.append((name, kind, lo, hi, u))
        where = range_text(kind, lo, hi)
        text = [
            "module",
            "",
            enc.import_line,
            "",
            "@[expose] public section",
            "",
            "/-!",
            f"# The saving with {enc.doc} on {where}: cells {part[0][0]} to {part[-1][0]}",
            "",
            "This file is generated by `python3 -m search.certs`; do not edit it. Each lemma"
            " bounds",
            f"`{enc.fn_text}` on one cell `[c₁, c₂]` by `F(A(c₁), Γ(c₂))`, with certified"
            " rational bounds",
            "on `A(c₁)` and `Γ(c₂)`; the last lemma joins the cells.",
            "-/",
            "",
            "namespace ImprovedExponents",
            "",
            "open Set",
            "",
        ]
        for index, cell in part:
            text += [cell_lemma(index, cell, enc), ""]
        doc = (f"`{enc.fn_text} < {dec(u)}` for `c` in {where}: cells {part[0][0]} to"
               f" {part[-1][0]}.")
        text += [chain_lemma(name, doc, kind, lo, hi, u,
                             [f"{enc.lemma}_cell_{i}" for i, _ in part], enc),
                 "", "end ImprovedExponents", ""]
        out[f"{enc.prefix}{number}.lean"] = "\n".join(text)

    base = os.path.basename
    text = ["module", ""]
    text += [f"public import {enc.module_dir}{base(enc.prefix)}{n}"
             for n in range(1, len(blocks) + 1)]
    text += [
        "",
        "@[expose] public section",
        "",
        "/-!",
        f"# The saving with {enc.doc} on `({dec(enc.c_min)}, {dec(enc.c_max)}]`",
        "",
        "This file is generated by `python3 -m search.certs`; do not edit it. It joins the",
        f"{len(cells)} cells of the files `{base(enc.prefix)}1.lean` to"
        f" `{base(enc.prefix)}{len(blocks)}.lean` into three ranges:",
        "",
        f"* `{enc.lemma}_lt_below`: `{enc.fn_text} < {dec(enc.u_out)}` for"
        f" `{dec(enc.c_min)} < c ≤ {dec(enc.win_lo)}`;",
        f"* `{enc.lemma}_lt_window`: `{enc.fn_text} < {dec(enc.u_in)}` for"
        f" `{dec(enc.win_lo)} ≤ c ≤ {dec(enc.win_hi)}`;",
        f"* `{enc.lemma}_lt_above`: `{enc.fn_text} < {dec(enc.u_out)}` for"
        f" `{dec(enc.win_hi)} ≤ c ≤ {dec(enc.c_max)}`.",
    ] + ([
        "",
        f"For a shape it also has the tail `{enc.lemma}_lt_tail` (`c ≥ {dec(enc.c_max)}`) and"
        " the witness",
        f"`{enc.lemma}_witness` at `c = {dec(enc.witness.c)}`.",
    ] if enc.kind == "shape" else []) + [
        "-/",
        "",
        "namespace ImprovedExponents",
        "",
        "open Set",
        "",
    ]
    for name, kind, lo, hi, u in (
            (f"{enc.lemma}_lt_below", "Ioc", enc.c_min, enc.win_lo, enc.u_out),
            (f"{enc.lemma}_lt_window", "Icc", enc.win_lo, enc.win_hi, enc.u_in),
            (f"{enc.lemma}_lt_above", "Icc", enc.win_hi, enc.c_max, enc.u_out)):
        parts = [b[0] for b in blocks if lo <= b[2] < hi]
        doc = f"`{enc.fn_text} < {dec(u)}` for `c` in {range_text(kind, lo, hi)}."
        text += [chain_lemma(name, doc, kind, lo, hi, u, parts, enc), ""]
    if enc.kind == "shape":
        text += [tail_lemma(enc), "", witness_lemma(enc), ""]
    text += ["end ImprovedExponents", ""]
    out[f"{enc.join_name}.lean"] = "\n".join(text)
    return out


def print_stats(enc, cells):
    print(f"== {enc.name}: {enc.statement}")
    for i, cell in enumerate(cells, start=1):
        print(f"{i:4d}  [{dec(cell.c1)}, {dec(cell.c2)}]  u = {dec(cell.u)}  "
              f"alo = {dec(cell.base.alo)}  theta = {dec(cell.gam.theta)}  "
              f"ghi = {dec(cell.gam.ghi)}")
    tail = tail_base(enc)
    print(f"tail  [{dec(enc.c_max)}, oo)  alo = {dec(tail.alo)}  k = {tail.k}  "
          f"ok = {enc.saving_ok(tail.alo, Fr(2, 3), enc.u_out)}")


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--check", action="store_true", help="compare with the files on disk")
    parser.add_argument("--stats", action="store_true", help="print the cells")
    parser.add_argument("--encoding", default="all",
                        help="`pruned`, `full`, `both`, `shapes`, a shape such as `S24`, or `all`"
                             " (default)")
    parser.add_argument("--out", default=LEAN_DIR, help="directory of the Lean files")
    args = parser.parse_args(argv)
    which = args.encoding
    if which == "all":
        encodings = [PRUNED, FULL] + shapes()
    elif which == "both":
        encodings = [PRUNED, FULL]
    elif which == "shapes":
        encodings = shapes()
    elif which in ENCODINGS:
        encodings = [ENCODINGS[which]]
    elif re.fullmatch(r"S\d\d", which):
        encodings = [shape(int(which[1]), int(which[2]))]
    else:
        parser.error(f"unknown encoding {which}")
    status = 0
    for enc in encodings:
        cells = make_cells(enc)
        if args.stats:
            print_stats(enc, cells)
            continue
        files = render(cells, enc)
        for name, text in sorted(files.items()):
            path = os.path.join(args.out, name)
            if args.check:
                with open(path, encoding="utf-8") as f:
                    same = f.read() == text
                print(f"{name}: {'ok' if same else 'DIFFERENT'}")
                status |= not same
            else:
                with open(path, "w", encoding="utf-8") as f:
                    f.write(text)
                print(f"wrote {path} ({text.count(chr(10))} lines)")
        if enc.kind == "shape" and not args.check:
            print(f"{enc.name}: sup = {enc.sup:.9f} at c = {enc.c_star:.4f}, window"
                  f" [{dec(enc.win_lo)}, {dec(enc.win_hi)}], c_max = {dec(enc.c_max)},"
                  f" witness ok = {enc.witness.valid()}")
        print(f"{enc.name}: {len(cells)} cells in {len(files) - 1} files")
    return status


if __name__ == "__main__":
    sys.exit(main())
