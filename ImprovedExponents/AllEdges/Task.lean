module

public import ThreeSumApsp.Programs.Tasks
public import ThreeSumApsp.Programs.Sec3.Theorem17.Witnesses.Scan

@[expose] public section

/-!
# All-edges Exact Triangle as a task

Footnote 10 of the paper: the proof of Theorem 17 "also solves the all-edges version of Exact
Triangle (scanning each pair only until its zero triangle is found), to which the (min,+)-product
reduces on the same `n` vertices".  The all-edges version asks, for every pair `(a, b)` of the two
outer parts, whether it lies in a zero triangle.

This file fixes the task (`aeTask`), in the calling convention of upstream's tasks
(`Light.Sec3.pairsTask` is the pattern): ae(n, U, ab, bc, ac, out, fr) writes `n²` flags to `out`,
cell `a n + b` holding 1 if `w(a,b) + w(b,c) + w(a,c) = 0` for some `c` and 0 if not (`aeFlags`).
-/

namespace ImprovedExponents.AllEdges

open Light Light.Sec3 ThreeSumApsp ThreeSumApsp.Spec

/-- Three `n × n` matrices of weights in the memory, and the place for `n²` flags. -/
structure AeInst : Type where
  n : ℕ
  U : ℕ
  ab : ℕ
  bc : ℕ
  ac : ℕ
  out : ℕ
  AB : List ℤ
  BC : List ℤ
  AC : List ℤ

/-- The three matrices and the place for the flags lie below the free pointer, the entries of the
matrices are bounded by `U`, and the place for the flags does not meet the matrices. -/
structure AeInst.Pre (x : AeInst) (μ : ℕ → ℤ) (fr : ℕ) : Prop where
  n_pos : 1 ≤ x.n
  U_pos : 1 ≤ x.U
  lenAB : x.AB.length = x.n * x.n
  lenBC : x.BC.length = x.n * x.n
  lenAC : x.AC.length = x.n * x.n
  segAB : Seg μ x.ab x.AB
  segBC : Seg μ x.bc x.BC
  segAC : Seg μ x.ac x.AC
  leAB : AbsLe x.AB x.U
  leBC : AbsLe x.BC x.U
  leAC : AbsLe x.AC x.U
  belowAB : x.ab + x.n * x.n ≤ fr
  belowBC : x.bc + x.n * x.n ≤ fr
  belowAC : x.ac + x.n * x.n ≤ fr
  belowOut : x.out + x.n * x.n ≤ fr
  apartAB : Apart x.ab (x.n * x.n) x.out (x.n * x.n)
  apartBC : Apart x.bc (x.n * x.n) x.out (x.n * x.n)
  apartAC : Apart x.ac (x.n * x.n) x.out (x.n * x.n)

/-- The three matrices of an instance, as a `TriInst` (the instance of upstream's `etTask`). -/
def AeInst.tri (x : AeInst) : TriInst := ⟨x.n, x.U, x.ab, x.bc, x.ac, x.AB, x.BC, x.AC⟩

/-- The matrices of an all-edges instance form an instance of Exact Triangle. -/
theorem AeInst.Pre.tri {x : AeInst} {μ : ℕ → ℤ} {fr : ℕ} (h : x.Pre μ fr) : x.tri.Pre μ fr :=
  { h with }

/-- An instance stays where it is if no cell below the free pointer changes, except the flags. -/
theorem AeInst.Pre.keep {x : AeInst} {μ μ' : ℕ → ℤ} {fr : ℕ} (h : x.Pre μ fr)
    (hs : KeptBut μ μ' fr x.out (x.n * x.n) := by light_keep) : x.Pre μ' fr := by
  light_facts h
  exact { h with segAB := h.segAB.keep, segBC := h.segBC.keep, segAC := h.segAC.keep }

/-- The flags: cell `a n + b` holds 1 if `w(a,b) + w(b,c) + w(a,c) = 0` for some `c < n`, and 0 if
not; the pair `(a, b)` of the cell `q < n²` is `(q / n, q % n)`. -/
noncomputable def aeFlags (n : ℕ) (AB BC AC : List ℤ) : List ℤ :=
  (List.range (n * n)).map fun q =>
    flag (∃ c < n, AB.getD q 0 + BC.getD (q % n * n + c) 0 + AC.getD (q / n * n + c) 0 = 0)

@[simp] theorem length_aeFlags (n : ℕ) (AB BC AC : List ℤ) :
    (aeFlags n AB BC AC).length = n * n := by
  simp [aeFlags]

/-- The flag of the cell `q < n²`. -/
theorem aeFlags_getD {n : ℕ} (AB BC AC : List ℤ) {q : ℕ} (hq : q < n * n) :
    (aeFlags n AB BC AC).getD q 0 =
      flag (∃ c < n, AB.getD q 0 + BC.getD (q % n * n + c) 0 + AC.getD (q / n * n + c) 0 = 0) := by
  simp [aeFlags, List.getD_eq_getElem?_getD, hq]

/-- The flag of the pair `(a, b)`, in terms of the scan of the whole part `C` (upstream's
`scanHit n AB BC AC a b 0 n`, the pure function behind the brute force of Theorem 17). -/
theorem aeFlags_getD_eq_bit_scanHit {n : ℕ} (AB BC AC : List ℤ) {a b : ℕ} (ha : a < n)
    (hb : b < n) :
    (aeFlags n AB BC AC).getD (a * n + b) 0 = bit (scanHit n AB BC AC a b 0 n) := by
  have hq : a * n + b < n * n := by nlinarith
  have hdiv : (a * n + b) / n = a := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hb]
    simp
  have hmod : (a * n + b) % n = b := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]
  rw [aeFlags_getD _ _ _ hq, hdiv, hmod, ← flag_eq_bit]
  congr 1
  simp only [scanHit, List.any_eq_true, List.mem_range, decide_eq_true_eq, Nat.add_zero]

/-- **All-edges Exact Triangle**: ae(n, U, ab, bc, ac, out, fr) writes the `n²` flags to `out`. -/
noncomputable def aeTask : Task where
  Inst := AeInst
  size x := x.n
  bound x := x.U
  args x := [x.n, x.U, x.ab, x.bc, x.ac, x.out]
  Pre := AeInst.Pre
  Post x μ fr _ μ' := Seg μ' x.out (aeFlags x.n x.AB x.BC x.AC) ∧ KeptBut μ μ' fr x.out (x.n * x.n)

end ImprovedExponents.AllEdges
