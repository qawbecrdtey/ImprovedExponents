import math
import unittest

from search.exponents import (
    LN4, R, apsp, apsp_all_edges, baselines, box_gamma, cor32_gamma, eps_star, et_saving,
    lemma11_finite_gamma, maxmin_gamma, pruned_yates_profile, query_exp, theta_for_query,
    three_sum,
)

# Table 2 of the paper: for each ratio c, the row's eps, then gamma for the query
# exponents q in Q_COLUMNS (left half) and for the densities kappa in K_COLUMNS
# (right half). The paper rounds all values down.
Q_COLUMNS = [0.10, 0.25, None, 0.50, 0.75, 0.90]  # None: theta = 1/9, q = 0.4277...
K_COLUMNS = [0.10, 0.25, 0.50, 0.75, 1.00]
TABLE_2 = {
    40: (0.029, [0.0205, 0.0608, 0.1175, 0.1429, 0.2417, 0.3095],
         [0.0166, 0.0473, 0.1060, 0.1720, 0.2442]),
    21: (0.056, [0.0112, 0.0331, 0.0640, 0.0778, 0.1316, 0.1685],
         [0.0099, 0.0286, 0.0653, 0.1074, 0.1546]),
    19: (0.062, [0.0097, 0.0287, 0.0555, 0.0675, 0.1142, 0.1463],
         [0.0087, 0.0253, 0.0578, 0.0954, 0.1379]),
    15: (0.079, [0.0061, 0.0183, 0.0354, 0.0430, 0.0728, 0.0932],
         [0.0057, 0.0168, 0.0389, 0.0646, 0.0941]),
    12: (0.099, [0.0028, 0.0083, 0.0160, 0.0195, 0.0330, 0.0423],
         [0.0027, 0.0080, 0.0186, 0.0312, 0.0459]),
    10.5: (0.114, [0.0007, 0.0022, 0.0043, 0.0052, 0.0089, 0.0114],
           [0.0007, 0.0022, 0.0052, 0.0087, 0.0129]),
}


def rounded_down(table_value, value, digits):
    return table_value <= value < table_value + 10 ** -digits


class PaperConstants(unittest.TestCase):
    def test_corollary_26(self):
        self.assertAlmostEqual(box_gamma(21, 1 / 9), math.log(20 / 9) / (9 * LN4), places=12)
        self.assertTrue(rounded_down(0.0640, box_gamma(21, 1 / 9), 4))
        self.assertTrue(rounded_down(0.4277, query_exp(1 / 9), 4))

    def test_theorem_5(self):
        self.assertAlmostEqual(box_gamma(19, 1 / 9), 1 / 18, places=12)

    def test_eps_star(self):
        self.assertAlmostEqual(eps_star(), 0.120412, places=6)
        self.assertLess(R(10.0001, 0), eps_star())
        self.assertAlmostEqual(R(10.0001, 0), eps_star(), places=4)

    def test_table_2(self):
        for c, (eps, left, right) in TABLE_2.items():
            gammas = [box_gamma(c, 1 / 9 if q is None else theta_for_query(q)) for q in Q_COLUMNS]
            gammas += [cor32_gamma(c, kappa) for kappa in K_COLUMNS]
            for expected, got in zip(left + right, gammas):
                self.assertTrue(rounded_down(expected, got, 4), (c, expected, got))
            # A row's eps is the smallest R_c(gamma) over its entries.
            self.assertTrue(rounded_down(eps, min(R(c, g) for g in gammas), 3), c)

    def test_theorem_22(self):
        self.assertAlmostEqual(three_sum(et_saving(1 / 18, 1 / 18)), 2 - 1 / 1296, places=12)
        self.assertAlmostEqual(apsp(et_saving(1 / 18, 1 / 18)), 3 - 1 / 1944, places=12)
        et = et_saving(0.063, 1 / 18)
        self.assertAlmostEqual(et, 0.00175, places=12)
        self.assertAlmostEqual(three_sum(et), 1.999125, places=12)
        self.assertLess(apsp(et), 2.99942)
        self.assertAlmostEqual(apsp_all_edges(et), 2.99825, places=12)


class Levers(unittest.TestCase):
    def test_maxmin_beats_split_at_m_over_9(self):
        # Lemma 11 taken exactly is at least the split at d = m/9 used in Section 2.
        self.assertGreater(maxmin_gamma(19, 0.5), 1 / 18)
        self.assertGreater(maxmin_gamma(21, 0.5), cor32_gamma(21, 0.5))

    def test_maxmin_matches_finite_sums(self):
        for c in (15, 21, 30):
            self.assertAlmostEqual(lemma11_finite_gamma(c, 0.5, 800), maxmin_gamma(c, 0.5),
                                   delta=0.003)

    def test_pruned_yates_last_stage_dominates(self):
        for c in (10.5, 15, 21, 40):
            for m in (20, 60):
                profile = pruned_yates_profile(c, m)
                self.assertEqual(max(range(len(profile)), key=profile.__getitem__),
                                 len(profile) - 1)
                # Stage sizes shrink by at least 7/9 per step back (NOTES.md).
                for k in range(len(profile) - 1):
                    self.assertLessEqual(profile[k], profile[k + 1] + math.log(7 / 9) + 1e-9)
                # The last stage is at most M/(1 - rho), rho = 9m/(L-m+1).
                L = round(c * m)
                self.assertLessEqual(profile[-1], -math.log(1 - 9 * m / (L - m + 1)) + 1e-9)

    def test_baselines(self):
        expected = [1.999228, 1.999125, 1.999075, 1.999073, 1.999016, 1.999000, 1.998970,
                    1.998952]
        got = [row["three_sum"] for row in baselines()]
        for e, g in zip(expected, got):
            self.assertAlmostEqual(e, g, delta=1e-6)
        self.assertEqual(sorted(got, reverse=True), got)


if __name__ == "__main__":
    unittest.main()
