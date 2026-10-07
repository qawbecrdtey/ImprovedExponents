import math
import os
import re
import unittest
from fractions import Fraction as Fr

from search import certs as C

GLOBAL_FILE = {"pruned": "Global.lean", "full": "GlobalFull.lean"}


class Enclosures(unittest.TestCase):
    def test_log_bounds_enclose_the_logarithm(self):
        for x in ("0.087", "0.1321", "0.9", "1.05", "9.5", "21.9153", "63", "199.087"):
            x = Fr(x)
            k = C.nearest_k(x)
            lo, hi = C.log_lo(k, x), C.log_hi(k, x)
            self.assertLess(lo, hi)
            self.assertLessEqual(float(lo), math.log(x) + 1e-12)
            self.assertGreaterEqual(float(hi), math.log(x) - 1e-12)
            self.assertLess(float(hi - lo), 4e-6)

    def test_nearest_power_of_two(self):
        self.assertEqual([C.nearest_k(Fr(x)) for x in ("0.116", "0.09", "9", "12", "21", "199")],
                         [-3, -3, 3, 4, 4, 8])

    def test_log_constants(self):
        for lo, hi, x in ((C.LOG2_LO, C.LOG2_HI, 2), (C.LOG3_LO, C.LOG3_HI, 3),
                          (C.LOG10_LO, C.LOG10_HI, 10)):
            self.assertLess(float(lo), math.log(x))
            self.assertLess(math.log(x), float(hi))

    def test_bounds_are_close_to_floating_point(self):
        for c in ("10.5", "21", "21.9153", "23", "60", "200"):
            c = Fr(c)
            g = C.GamBound(c)
            self.assertTrue(g.valid())
            self.assertGreaterEqual(float(g.ghi), C.gam(float(c)))
            self.assertLess(float(g.ghi) - C.gam(float(c)), 2e-6)
            for enc in (C.PRUNED, C.FULL):
                b = C.BaseBound(c, enc)
                self.assertTrue(b.valid())
                self.assertLessEqual(float(b.alo), enc.base_float(float(c)))
                self.assertLess(enc.base_float(float(c)) - float(b.alo), 2e-5)
        self.assertEqual(C.BaseBound(Fr(22)).alo, C.BaseBound(Fr(22), C.PRUNED).alo)

    def test_base_full_lo_is_the_hypothesis_of_le_baseFull(self):
        c, k = Fr("107.5") / 5, 4
        expected = (c * C.LOG10_LO - (C.c_ent_hi(k, c)) / 2 - (c - 1) * C.LOG3_HI)
        self.assertEqual(C.base_full_lo(k, c), expected)
        self.assertLess(C.c_ent_lo(k, c), C.c_ent_hi(k, c))
        self.assertAlmostEqual(float(C.c_ent_hi(k, c)), float(c) * C.H(1 / float(c)), delta=2e-6)

    def test_reference_values(self):
        self.assertAlmostEqual(C.saving(21.915), 0.00209531, delta=2e-9)
        self.assertAlmostEqual(C.saving(21), 0.0020927, delta=1e-7)
        self.assertAlmostEqual(C.saving(23), 0.0020922, delta=1e-7)
        self.assertAlmostEqual(C.theta_star(22), 0.1160367, delta=1e-7)
        self.assertAlmostEqual(C.saving(21.3816, C.FULL), 0.00205991, delta=2e-9)
        self.assertAlmostEqual(C.saving(21.4, C.FULL), 0.00205991, delta=2e-9)
        self.assertAlmostEqual(C.saving(21, C.FULL), 0.0020594, delta=1e-7)
        self.assertAlmostEqual(C.saving(22, C.FULL), 0.0020588, delta=1e-7)
        self.assertAlmostEqual(C.base_full(21.4), 24.8438, delta=1e-4)
        self.assertEqual(C.saving(22), C.PRUNED.saving(22))

    def test_encodings(self):
        self.assertEqual((C.C_MIN, C.WIN_LO, C.WIN_HI, C.C_MAX), (10, 21, 23, 200))
        self.assertEqual((C.U_OUT, C.U_IN), (C.PRUNED.u_out, C.PRUNED.u_in))
        self.assertEqual(C.STATEMENT, "savingF (basePruned c) (Gam c)")
        self.assertEqual(C.FULL.statement, "savingF (baseFull c) (Gam c)")
        self.assertEqual((C.FULL.win_lo, C.FULL.win_hi, C.FULL.c_max), (Fr("20.8"), 22, 200))
        self.assertEqual((C.FULL.u_out, C.FULL.u_in), (Fr("0.002059"), Fr("0.002061")))
        self.assertEqual(set(C.ENCODINGS), {"pruned", "full"})
        self.assertEqual(C.bound_for(Fr(21)), C.U_IN)
        self.assertEqual(C.bound_for(Fr(21), C.FULL), C.FULL.u_in)
        self.assertEqual(C.bound_for(Fr(22), C.FULL), C.FULL.u_out)

    def test_decimals(self):
        self.assertEqual([C.dec(Fr(x)) for x in ("21", "21.03", "0.0349393", "0.002095", "-0.5")],
                         ["21", "21.03", "0.0349393", "0.002095", "-0.5"])
        self.assertRaises(ValueError, C.dec, Fr(1, 3))


class CellsMixin:
    """The tests of the cells of one encoding (`ENC`)."""

    ENC = None

    @classmethod
    def setUpClass(cls):
        cls.cells = C.make_cells(cls.ENC)
        cls.files = C.render(cls.cells, cls.ENC)

    def test_cells_cover_the_range(self):
        cells, enc = self.cells, self.ENC
        self.assertEqual(cells[0].c1, enc.c_min)
        self.assertEqual(cells[-1].c2, enc.c_max)
        for a, b in zip(cells, cells[1:]):
            self.assertEqual(a.c2, b.c1)
        for cell in cells:
            self.assertLess(cell.c1, cell.c2)
        ends = {cell.c2 for cell in cells}
        self.assertIn(enc.win_lo, ends)
        self.assertIn(enc.win_hi, ends)
        self.assertLess(len(cells), 400)

    def test_bound_of_each_cell(self):
        enc = self.ENC
        self.assertLess(enc.u_out, enc.u_in)
        self.assertLess(enc.u_in, Fr("0.0021"))
        for cell in self.cells:
            inside = enc.win_lo <= cell.c1 and cell.c2 <= enc.win_hi
            outside = cell.c2 <= enc.win_lo or enc.win_hi <= cell.c1
            self.assertTrue(inside or outside)
            self.assertEqual(cell.u, enc.u_in if inside else enc.u_out)

    def test_certificates_hold_exactly(self):
        for cell in self.cells:
            b, g = cell.base, cell.gam
            self.assertTrue(cell.valid())
            self.assertIs(b.enc, self.ENC)
            self.assertEqual((b.c, g.c), (cell.c1, cell.c2))
            # The hypotheses of `le_basePruned`/`le_baseFull`, `gammaX_le`, `gammaQ_le`, `Gam_le`.
            enc = self.ENC
            self.assertLessEqual(b.alo, enc.base_lo(b.k, b.c))
            self.assertLessEqual(enc.gamma_x_hi(g.k_x, g.c, g.theta), g.ghi)
            self.assertLessEqual(enc.gamma_q_hi(g.k_q, g.theta), g.ghi)
            self.assertTrue(0 < g.theta < enc.theta_max and g.ghi <= Fr(2, 3) and enc.c_min < g.c)
            # The last hypothesis of `savingF_lt_of_mem_Icc` / `shapeSaving_lt_of_mem_Icc`.
            log_b_hi = C.log_hi(enc.k_b, enc.b) if enc.kind == "shape" else 2 * C.LOG2_HI
            self.assertLess(g.ghi * (1 - 2 * cell.u) * log_b_hi, 2 * cell.u * b.alo)

    def test_cells_agree_with_floating_point(self):
        for cell in self.cells:
            lo, hi = float(cell.c1), float(cell.c2)
            for c in (max(lo, float(self.ENC.c_min) + 0.001), (lo + hi) / 2, hi):
                self.assertLess(self.ENC.saving(c), float(cell.u))

    def test_tail(self):
        enc = self.ENC
        tail = C.tail_base(enc)
        self.assertTrue(tail.valid())
        self.assertTrue(enc.saving_ok(tail.alo, Fr(2, 3), enc.u_out))
        if enc.kind == "shape":
            text = self.files[f"{enc.join_name}.lean"]
            self.assertIn(f"(le_basePrunedS {tail.k} {enc.k_s} :\n    ({C.dec(tail.alo)} : ℝ) ≤ "
                          f"{enc.base} {C.dec(enc.c_max)}) hc", text)
        else:
            with open(os.path.join(C.LEAN_DIR, GLOBAL_FILE[enc.name]), encoding="utf-8") as f:
                text = f.read()
            self.assertIn(f"({enc.le_base} {tail.k} : ({C.dec(tail.alo)} : ℝ) ≤ "
                          f"{enc.base} {C.dec(enc.c_max)})", text)
        tail_proof = " :=" if enc.kind == "shape" else " := by"
        self.assertIn(f"{enc.statement} < {C.dec(enc.u_in)}{tail_proof}", text)
        self.assertIn(f"{len(self.cells)} cells", text)

    def test_generation_is_deterministic(self):
        self.assertEqual(C.render(C.make_cells(self.ENC), self.ENC), self.files)

    def test_lean_files_on_disk(self):
        enc = self.ENC
        folder, stem = os.path.split(enc.prefix)
        names = os.listdir(os.path.join(C.LEAN_DIR, folder))
        on_disk = {os.path.join(folder, name) for name in names
                   if re.fullmatch(rf"{stem}\d*\.lean", name)
                   or name == os.path.basename(enc.join_name) + ".lean"}
        self.assertEqual(on_disk, set(self.files))
        for name, text in self.files.items():
            with open(os.path.join(C.LEAN_DIR, name), encoding="utf-8") as f:
                self.assertEqual(f.read(), text, name)

    def test_lean_text(self):
        enc = self.ENC
        whole = "".join(self.files.values())
        for line in whole.splitlines():
            self.assertLessEqual(len(line), 100, line)
        for word in ("sorry", "axiom", "native_decide", "maxHeartbeats"):
            self.assertNotIn(word, whole)
        names = re.findall(rf"^theorem {enc.lemma}_cell_(\d+) :", whole, flags=re.M)
        self.assertEqual([int(n) for n in names], list(range(1, len(self.cells) + 1)))
        for index, cell in enumerate(self.cells, start=1):
            self.assertIn(C.cell_lemma(index, cell, enc), whole)
        for name in (f"{enc.join_name}.lean", f"{enc.prefix}1.lean"):
            self.assertTrue(self.files[name].endswith("end ImprovedExponents\n"))
        self.assertLessEqual(max(len(part) for part in C.split_files(self.cells, enc)),
                             C.MAX_CELLS_PER_FILE)
        for suffix in ("below", "window", "above"):
            self.assertIn(f"theorem {enc.lemma}_lt_{suffix} :", self.files[f"{enc.join_name}.lean"])
        others = [e for e in (C.PRUNED, C.FULL, *C.shapes()) if e is not enc]
        for other in others:
            self.assertNotIn(other.lemma, whole)
            self.assertNotIn(other.statement, whole)


class CellsPruned(CellsMixin, unittest.TestCase):
    ENC = C.PRUNED

    def test_pruned_defaults(self):
        self.assertEqual(C.render(C.make_cells()), self.files)
        self.assertEqual(C.cell_lemma(1, self.cells[0]), C.cell_lemma(1, self.cells[0], C.PRUNED))
        self.assertEqual(len(self.cells), 222)


class CellsFull(CellsMixin, unittest.TestCase):
    ENC = C.FULL

    def test_window_holds_the_maximum(self):
        best = max(self.ENC.saving(20.8 + 0.01 * i) for i in range(121))
        self.assertGreater(best, float(self.ENC.u_out))
        self.assertLess(best, float(self.ENC.u_in))
        self.assertLess(self.ENC.saving(20.8), float(self.ENC.u_out))
        self.assertLess(self.ENC.saving(22), float(self.ENC.u_out))


class ShapeMixin(CellsMixin):
    """The tests of the cells of one shape, plus its window, tail and witness."""

    KN = None
    TABLE = None  # the value of the paper's Table 2 (search/family.py)

    @classmethod
    def setUpClass(cls):
        cls.ENC = C.shape(*cls.KN)
        super().setUpClass()

    def test_shape_constants(self):
        enc, (k, n) = self.ENC, self.KN
        self.assertEqual((enc.s, enc.b), (k * n, (k - 1) * (n - 1)))
        self.assertEqual(enc.c_min, enc.s + 1)
        self.assertEqual(enc.theta_max, Fr(enc.s, enc.s + 1))
        self.assertEqual((enc.k_s, enc.k_b), (C.nearest_k(Fr(enc.s)), C.nearest_k(Fr(enc.b))))
        self.assertEqual(enc.name, f"S{k}{n}")
        self.assertEqual(enc.statement, f"shapeSaving {enc.s} {enc.b} c")
        self.assertEqual(enc.prefix, f"Shapes/Cells_{enc.name}_")
        self.assertEqual(enc.join_name, f"Shapes/Cells_{enc.name}")
        self.assertLess(len(self.cells), 300 + 1)

    def test_enclosure_matches_the_table(self):
        enc = self.ENC
        self.assertEqual(enc.u_in - enc.u_out, 2 * Fr(1, 10 ** 6))
        self.assertAlmostEqual(float(enc.u_out + Fr(1, 10 ** 6)), enc.sup, places=6)
        self.assertAlmostEqual(enc.sup, self.TABLE, delta=5e-7)
        self.assertLess(float(enc.u_out), enc.sup)
        self.assertLess(enc.sup, float(enc.u_in))

    def test_matches_family(self):
        from search.family import Group, schoenhage, score
        enc, (k, n) = self.ENC, self.KN
        sc = score([Group(schoenhage(k, n), 1.0, enc.c_star)])
        self.assertAlmostEqual(sc["et"], enc.sup, places=7)
        self.assertAlmostEqual(sc["et"], float(enc.u_out), places=4)
        self.assertAlmostEqual(sc["et"], float(enc.u_in), places=4)

    def test_window_holds_the_maximum(self):
        enc = self.ENC
        lo, hi = float(enc.win_lo), float(enc.win_hi)
        self.assertLess(lo, enc.c_star)
        self.assertLess(enc.c_star, hi)
        self.assertLess(enc.saving(lo), float(enc.u_out))
        self.assertLess(enc.saving(hi), float(enc.u_out))
        self.assertGreater(float(enc.c_min), 0)

    def test_witness_holds_exactly(self):
        enc, w = self.ENC, self.ENC.witness
        self.assertTrue(w.valid())
        self.assertTrue(float(enc.win_lo) < float(w.c) < float(enc.win_hi))
        self.assertLess(float(enc.u_out), enc.saving(float(w.c)))
        # The hypotheses of `basePrunedS_le`, `le_gammaXS`, `le_gammaQS`, `lt_savingS`.
        self.assertLessEqual(C.base_s_hi(w.k, enc.k_s, enc.s, w.c), w.ahi)
        self.assertLessEqual(w.glo, C.gamma_x_s_lo(w.k_x, enc.k_s, enc.k_b, enc.s, enc.b, w.c,
                                                  w.theta))
        self.assertLessEqual(w.glo, C.gamma_q_s_lo(w.k_q, enc.k_s, enc.k_b, enc.s, enc.b, w.theta))
        self.assertLess(2 * enc.u_out * w.ahi,
                        w.glo * (1 - 2 * enc.u_out) * C.log_lo(enc.k_b, enc.b))
        text = self.files[f"{enc.join_name}.lean"]
        self.assertIn(C.witness_lemma(enc), text)
        self.assertIn(C.tail_lemma(enc), text)
        self.assertIn(f"theorem {enc.lemma}_witness : ({C.dec(enc.u_out)} : ℝ) < "
                      f"shapeSaving {enc.s} {enc.b} {C.dec(w.c)} :=", text)

    def test_parametric_enclosures_specialize_to_the_main_shape(self):
        c, theta = Fr("21.9"), Fr("0.1161")
        kx, kq, kc = C.nearest_k(c - 1), C.nearest_k(theta), C.nearest_k(c)
        ks, kb = C.nearest_k(Fr(9)), C.nearest_k(Fr(4))
        self.assertAlmostEqual(float(C.gamma_x_s_hi(kx, ks, kb, 9, 4, c, theta)),
                               float(C.gamma_x_hi(kx, c, theta)), delta=1e-6)
        self.assertAlmostEqual(float(C.gamma_q_s_hi(kq, ks, kb, 9, 4, theta)),
                               float(C.gamma_q_hi(kq, theta)), delta=1e-6)
        self.assertAlmostEqual(float(C.base_s_lo(kc, ks, 9, c)),
                               float(C.base_pruned_lo(kc, c)), delta=1e-4)
        self.assertLess(C.gamma_x_s_lo(kx, ks, kb, 9, 4, c, theta),
                        C.gamma_x_s_hi(kx, ks, kb, 9, 4, c, theta))
        self.assertLess(C.gamma_q_s_lo(kq, ks, kb, 9, 4, theta),
                        C.gamma_q_s_hi(kq, ks, kb, 9, 4, theta))
        self.assertLess(C.base_s_lo(kc, ks, 9, c), C.base_s_hi(kc, ks, 9, c))


class ShapeS24(ShapeMixin, unittest.TestCase):
    KN, TABLE = (2, 4), 0.001876


class ShapeS34(ShapeMixin, unittest.TestCase):
    KN, TABLE = (3, 4), 0.001868


class ShapeS25(ShapeMixin, unittest.TestCase):
    KN, TABLE = (2, 5), 0.001777


class ShapeS23(ShapeMixin, unittest.TestCase):
    KN, TABLE = (2, 3), 0.001670


class ShapeS26(ShapeMixin, unittest.TestCase):
    KN, TABLE = (2, 6), 0.001624


class ShapeS35(ShapeMixin, unittest.TestCase):
    KN, TABLE = (3, 5), 0.001614


class ShapeS44(ShapeMixin, unittest.TestCase):
    KN, TABLE = (4, 4), 0.001574


class ShapeS45(ShapeMixin, unittest.TestCase):
    KN, TABLE = (4, 5), 0.001324


class ShapeS55(ShapeMixin, unittest.TestCase):
    KN, TABLE = (5, 5), 0.001099


class ShapesTable(unittest.TestCase):
    def test_shape_list_and_cli(self):
        self.assertEqual(len(C.SHAPE_LIST), 9)
        self.assertNotIn((3, 3), C.SHAPE_LIST)
        self.assertIs(C.shape(2, 4), C.shape(2, 4))
        self.assertEqual([e.name for e in C.shapes()],
                         [f"S{k}{n}" for k, n in C.SHAPE_LIST])

    def test_table_file_cites_the_generated_lemmas(self):
        with open(os.path.join(C.LEAN_DIR, "Shapes", "Table.lean"), encoding="utf-8") as f:
            text = f.read()
        for enc in C.shapes():
            self.assertIn(f"import ImprovedExponents.Optimum.Shapes.Cells_{enc.name}\n", text)
            self.assertIn(f"theorem {enc.lemma}_lt (c : ℝ) (hc : {C.dec(enc.c_min)} < c) :"
                          f" shapeSaving {enc.s} {enc.b} c < {C.dec(enc.u_in)} :=", text)
            self.assertIn(f"theorem {enc.lemma}_gt : ({C.dec(enc.u_out)} : ℝ) < "
                          f"shapeSaving {enc.s} {enc.b} {C.dec(enc.witness.c)} :=", text)
            self.assertIn(f"Ioi {C.dec(enc.c_min)}) ∈ Ioc ({C.dec(enc.u_out)} : ℝ)"
                          f" {C.dec(enc.u_in)} :=", text)
        self.assertIn("theorem shapes_table :", text)
        self.assertIn("(0.002095 : ℝ) < shapeSaving 9 4 22", text)
        for line in text.splitlines():
            self.assertLessEqual(len(line), 100, line)


if __name__ == "__main__":
    unittest.main()
