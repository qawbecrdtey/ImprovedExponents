import unittest

from search import exponents as E
from search.family import Group, gamma, ln_D, ln_N_min, schoenhage, score

S33 = schoenhage(3, 3)


class SingleShape(unittest.TestCase):
    def test_matches_exponents(self):
        for c in (12, 21, 30):
            sched = [Group(S33, 1.0, c)]
            for kappa in (0.5, 0.52):
                self.assertAlmostEqual(gamma(sched, kappa), E.maxmin_gamma(c, kappa), places=7)
            self.assertAlmostEqual(ln_D(sched) / ln_N_min(sched, 0.07), E.R_pruned(c, 0.07),
                                   places=10)

    def test_best_baseline(self):
        sc = score([Group(S33, 1.0, 21.915)])
        self.assertAlmostEqual(sc["et"], 0.0020953, delta=2e-7)

    def test_family_parameters(self):
        self.assertEqual((S33.s, S33.b), (9, 4))
        self.assertEqual((schoenhage(2, 4).s, schoenhage(2, 4).b), (8, 3))

    def test_table_2(self):
        """The nine other shapes of the family at their optimal c (the paper's Table 2); the Lean
        certificates of ImprovedExponents/Optimum/Shapes/ enclose these values within 1e-6."""
        table = {(2, 4): (20.11, 0.001876), (3, 4): (27.96, 0.001868), (2, 5): (24.24, 0.001777),
                 (2, 3): (16.03, 0.001670), (2, 6): (28.39, 0.001624), (3, 5): (34.04, 0.001614),
                 (4, 4): (35.96, 0.001574), (4, 5): (44.01, 0.001324), (5, 5): (54.02, 0.001099)}
        for (k, n), (c, et) in table.items():
            shape = schoenhage(k, n)
            self.assertLess(shape.b, (shape.s + 1) ** 2)
            self.assertAlmostEqual(score([Group(shape, 1.0, c)])["et"], et, delta=6e-7)


class Mixtures(unittest.TestCase):
    def test_proportional_split_is_neutral(self):
        whole = score([Group(S33, 1.0, 21.0)])
        split = score([Group(S33, 0.3, 0.3 * 21.0), Group(S33, 0.7, 0.7 * 21.0)])
        for key in ("gamma", "eps", "et"):
            self.assertAlmostEqual(whole[key], split[key], places=6)

    def test_non_proportional_split_is_no_better(self):
        whole = score([Group(S33, 1.0, 21.0)])
        split = score([Group(S33, 0.5, 0.5 * 15.0), Group(S33, 0.5, 0.5 * 27.0)])
        self.assertLessEqual(split["et"], whole["et"] + 1e-9)


if __name__ == "__main__":
    unittest.main()
