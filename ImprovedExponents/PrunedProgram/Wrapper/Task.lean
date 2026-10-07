module

public import ImprovedExponents.Pipeline.ThinClaim
public import ImprovedExponents.PrunedProgram.Wrapper.Offline

@[expose] public section

/-!
# The pruned offline routine solves the thin-product task

`offline32P_meets_thinTask` is `offline32_meets_thinTask` (`ImprovedExponents.Pipeline.ThinClaim`)
for the pruned routine: where the hypotheses of Theorem 30 hold from the threshold on, a program
in which `offline32P` meets `OfflineSpec32P` solves the thin-product task within `tOffline32P`.
The limits the routine needs are upstream's (`Lim31`), since the pruned shared stage has the same
layout and forms the same numbers, so `lim31_of_need` applies verbatim.
-/

namespace ImprovedExponents

open ThreeSumApsp ThreeSumApsp.Spec Light Light.Sec4

/-- **Where the hypotheses of Theorem 30 hold from the threshold on**, the pruned offline routine
solves the task. -/
-- adapted from ImprovedExponents/Pipeline/ThinClaim.lean (offline32_meets_thinTask)
theorem offline32P_meets_thinTask {lim : Limits} {P : Program} {G : RatParams} {c d : ℕ}
    (task : OfflineSpec32P lim P c G) {x : ThinInst} {μ : ℕ → ℤ} {fr : ℕ} (hpre : x.Pre μ fr)
    (hfit : G.m₀ ≤ logFour x.D → Hyp30 (parOf G x.N x.D) (switchOf31 G x.D))
    (ok : (offline32Need G x.N x.D x.U).Ok lim fr d) :
    Meets lim P Proc.offline32P (d + 1) [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out, fr] μ
      (tOffline32P c G x.N x.D x.w) fun r μ' => thinTask.Post x μ fr r μ' := by
  have hU0 : (0 : ℤ) ≤ (x.U : ℤ) := by positivity
  have hdepth : d + (G.a * (4 * x.D) + 12) ≤ lim.depth := ok.depth
  have hm4 := logFour_le_four_mul hpre.D_pos
  have hL : G.L (logFour x.D) ≤ G.a * (4 * x.D) :=
    (ratParams_L_le_mul G _).trans (Nat.mul_le_mul_left _ hm4)
  have spec := task x.N x.D x.x x.y x.wi x.wj x.out fr (thinMX x) (thinMY x) (x.U : ℤ) (x.U : ℤ) μ
    x.WI x.WJ
    { one_le_D := hpre.D_pos, one_le_N := hpre.N_pos
      lim := lim31_of_need hpre.D_pos hfit ok
      absX := fun i j => hpre.leX.abs_getD_le hU0 _
      absY := fun i j => hpre.leY.abs_getD_le hU0 _
      belowX := hpre.belowX, belowY := hpre.belowY }
    { matX := matAt_thinMX hpre, matY := matAt_thinMY hpre
      rows := hpre.segWI, cols := hpre.segWJ
      length_eq := by rw [hpre.lenWI, hpre.lenWJ]
      rows_lt := hpre.ltWI, cols_lt := hpre.ltWJ
      rows_le := by rw [hpre.lenWI]; exact hpre.belowWI
      cols_le := by rw [hpre.lenWI]; exact hpre.belowWJ
      out_le := by rw [hpre.lenWI]; exact hpre.belowOut
      out_matX := by rw [hpre.lenWI]; exact hpre.apartX
      out_matY := by rw [hpre.lenWI]; exact hpre.apartY
      out_rows := by rw [hpre.lenWI]; exact hpre.apartWI
      out_cols := by rw [hpre.lenWI]; exact hpre.apartWJ }
  rw [hpre.lenWI, map_entryN_thin hpre] at spec
  exact (spec _ (by omega)).mono le_rfl fun r μ' h => ⟨h.1, fun a ha => h.2 a ha.1 ha.2⟩

/-- The time of the pruned offline routine is monotone in the number of wanted positions. -/
-- adapted from ImprovedExponents/Pipeline/ThinClaim.lean (tOffline32_mono)
theorem tOffline32P_mono (c : ℕ) (G : RatParams) (N D₀ : ℕ) {w w' : ℕ} (hw : w ≤ w') :
    tOffline32P c G N D₀ w ≤ tOffline32P c G N D₀ w' := by
  unfold tOffline32P
  have := Nat.mul_le_mul_right (tQuery31 G D₀ + 30) hw
  omega

end ImprovedExponents
