module

public import ImprovedExponents.PrunedProgram.Wrapper.Preprocessing

@[expose] public section

/-!
# Corollary 32 with the pruned encoder: the offline routine

Upstream's `offline32` (`ThreeSumApsp/Programs/Sec4/ChoosingParameters/Offline.lean`) runs the
preprocessing and then asks one query for each wanted position.  `offline32P` is the same text with
`pre31P` in place of `pre31`; its specification `OfflineSpec32P` is upstream's `OfflineSpec32` for
the procedure `Proc.offline32P` with the time `tOffline32P`, and the proof is upstream's with
`PreSpec31P`, `QuerySpec31P` and `Ready31P`.

Adapted from upstream (Apache-2.0).
-/

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec ImprovedExponents

variable {lim : Limits} {P : Program} {G : RatParams} {N D₀ : ℕ} {X : Matrix (Fin N) (Fin D₀) ℤ}
  {Y : Matrix (Fin D₀) (Fin N) ℤ} {aX aY fr : ℕ} {U : ℤ} {μ μ' : ℕ → ℤ}

open Offline32 in
/-- offline32P(N, D, w, U, x, y, wi, wj, out, fr): preprocess with the pruned encoder, then ask one
query for each wanted position and store its answer. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Offline.lean (offline32Body)
def offline32PBody : Stmt :=
  .call Proc.pre31P [v Size, v Dim, v MatX, v MatY, v Free] Res ;;
  .for Pos (v Count) offlineAsk32

/-- What a query needs depends only on the cells of X, of Y, and on the cells from fr on. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Offline.lean (ready31_congr)
theorem ready31P_congr (h : Ready31P G X Y aX aY fr μ)
    (hX : ∀ a, aX ≤ a → a < aX + N * D₀ → μ' a = μ a)
    (hY : ∀ a, aY ≤ a → a < aY + D₀ * N → μ' a = μ a) (hfr : ∀ a, fr ≤ a → μ' a = μ a) :
    Ready31P G X Y aX aY fr μ' := by
  refine ⟨fun i j => ?_, fun i j => ?_, fun hs => ?_, fun hl => ?_⟩
  · rw [hX _ (by omega) ?_]
    · exact h.matX i j
    · have := Nat.mul_add_le_mul i.isLt (le_refl D₀)
      have := j.isLt
      omega
  · rw [hY _ (by omega) ?_]
    · exact h.matY i j
    · have := Nat.mul_add_le_mul i.isLt (le_refl N)
      have := j.isLt
      omega
  · rw [hfr _ le_rfl]
    exact h.small hs
  · obtain ⟨h1, h2, h3⟩ := h.large hl
    refine ⟨by rw [hfr _ le_rfl]; exact h1, by rw [hfr _ (by omega)]; exact h2,
      dsReadyP_congr h3 fun a ha => hfr a ?_⟩
    unfold blockAt at ha
    omega

/-- offline32P writes the wanted entries of XY to out. Below fr it changes only the output; nothing
is assumed about the cells from fr on. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Offline.lean (OfflineSpec32)
def OfflineSpec32P (lim : Limits) (P : Program) (c : ℕ) (G : RatParams) : Prop :=
  ∀ (N D₀ aX aY aI aJ out fr : ℕ) (X : Matrix (Fin N) (Fin D₀) ℤ) (Y : Matrix (Fin D₀) (Fin N) ℤ)
    (U : ℤ) (u : ℤ) (μ : ℕ → ℤ) (WI WJ : List ℕ),
    Input31 lim G X Y aX aY fr U → OfflineInput32 X Y aX aY aI aJ out fr WI WJ μ →
    ∀ d, d + (G.L (logFour D₀) + 8) ≤ lim.depth → Meets lim P Proc.offline32P d
      [N, D₀, WI.length, u, aX, aY, aI, aJ, out, fr] μ (tOffline32P c G N D₀ WI.length)
      fun _ μ' => Seg μ' out ((WI.zip WJ).map fun q => entryN X Y q.1 q.2) ∧
        ∀ a < fr, (a < out ∨ out + WI.length ≤ a) → μ' a = μ a

/-- The specification holds for the program with more procedures appended. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Offline.lean
-- (OfflineSpec32.append)
theorem OfflineSpec32P.append {c : ℕ} (h : OfflineSpec32P lim P c G) (R : Program) :
    OfflineSpec32P lim (P ++ R) c G :=
  fun N D₀ aX aY aI aJ out fr X Y U u μ WI WJ hg hin d hd =>
    (h N D₀ aX aY aI aJ out fr X Y U u μ WI WJ hg hin d hd).append R

/-- **One round**: the answer for position i joins the answers that are there. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Offline.lean
-- (offlineAsk32_ends)
theorem offlineAsk32P_ends (hq : QuerySpec31P lim P G) {aI aJ out d : ℕ}
    {u : ℤ} {WI WJ : List ℕ} (hg : Input31 lim G X Y aX aY fr U)
    (hin : OfflineInput32 X Y aX aY aI aJ out fr WI WJ μ) (hd : d + 4 ≤ lim.depth) {i : ℕ}
    (hi : i < WI.length) (r : ℤ)
    (hinv : Answered (Ready31P G X Y aX aY fr) (· < fr) out
      ((WI.zip WJ).map fun q => entryN X Y q.1 q.2) μ i μ') :
    Ends lim P d offlineAsk32 ⟨frame [N, D₀, WI.length, u, aX, aY, aI, aJ, out, fr, i, r], μ'⟩
      (tQuery31 G D₀ + 20) fun σ' => ∃ (r' : ℤ) (μ'' : ℕ → ℤ),
        σ' = ⟨frame [N, D₀, WI.length, u, aX, aY, aI, aJ, out, fr, i, r'], μ''⟩ ∧
        Answered (Ready31P G X Y aX aY fr) (· < fr) out
          ((WI.zip WJ).map fun q => entryN X Y q.1 q.2) μ (i + 1) μ'' := by
  have hw := hg.lim.std.space_le
  have hspace := hg.lim.space
  have hfr3 := add_three_le_structEnd G N D₀ fr
  have hlen := hin.length_eq
  have hrows := hin.rows_le
  have hcols := hin.cols_le
  have hout := hin.out_le
  have hiJ : i < WJ.length := by omega
  have hIN : WI[i] < N := hin.rows_lt _ (List.getElem_mem hi)
  have hJN : WJ[i] < N := hin.cols_lt _ (List.getElem_mem hiJ)
  -- the two indices are still in place
  have hrow : μ' (aI + i) = ((WI[i] : ℕ) : ℤ) :=
    (hinv.read hin.rows (j := i) (by simpa using hi)
      (by rcases hin.out_rows with h | h <;> omega) (by omega)).trans (List.getElem_map _)
  have hcol : μ' (aJ + i) = ((WJ[i] : ℕ) : ℤ) :=
    (hinv.read hin.cols (j := i) (by simpa using hiJ)
      (by rcases hin.out_cols with h | h <;> omega) (by omega)).trans (List.getElem_map _)
  -- Res := query31(mem[Rows + Pos], mem[Cols + Pos], N, D, x, y, fr)
  refine Ends.callToThen (hq N D₀ aX aY fr X Y U μ' ⟨WI[i], hIN⟩ ⟨WJ[i], hJN⟩ hg hinv.ready _
    (by omega)) ?_
    (ha := by light_side [hrow, hcol])
  rintro _ μ₂ ⟨rfl, hready, hquery⟩
  -- mem[Out + Pos] := Res
  light_store (out + i) ((X * Y) ⟨WI[i], hIN⟩ ⟨WJ[i], hJN⟩)
  have hstep := hinv.step (by simpa [hlen] using hi) hquery (fun j hj => Or.inl (by omega))
    (fun a ha => Or.inl (by omega)) (ready31P_congr hready
      (fun a h1 h2 => Function.update_of_ne (by rcases hin.out_matX with h | h <;> omega) _ _)
      (fun a h1 h2 => Function.update_of_ne (by rcases hin.out_matY with h | h <;> omega) _ _)
      fun a ha => Function.update_of_ne (by omega) _ _)
  rw [List.getElem_map, List.getElem_zip, entryN, dif_pos ⟨hIN, hJN⟩] at hstep
  exact ⟨_, _, rfl, hstep⟩

/-- offline32P meets its specification if the pruned preprocessing and the query meet theirs. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Offline.lean
-- (offline32_meets)
theorem offline32P_meets {c : ℕ} (hP : P[Proc.offline32P]? = some offline32PBody)
    (hpre : PreSpec31P lim P c G) (hq : QuerySpec31P lim P G) : OfflineSpec32P lim P c G := by
  intro N D₀ aX aY aI aJ out fr X Y U u μ WI WJ hg hin
  refine fun d hd => ⟨offline32PBody, hP, ?_⟩
  have hw := hg.lim.std.space_le
  have hspace := hg.lim.space
  have hfr3 := add_three_le_structEnd G N D₀ fr
  have hlen := hin.length_eq
  have hout := hin.out_le
  have hzip : (WI.zip WJ).length = WI.length := by simp [hlen]
  -- Res := pre31P(N, D, x, y, fr)
  refine Ends.callToThen (hpre N D₀ aX aY fr X Y U μ hg hin.matX hin.matY _ (by omega)) ?_
    (hT := by simp [tOffline32P]; omega)
  rintro r μ₁ ⟨hready, hblock⟩
  -- for Pos < Count: offlineAsk32
  refine Ends.for (fun i σ => ∃ (r : ℤ) (μ' : ℕ → ℤ),
      σ = ⟨frame [N, D₀, WI.length, u, aX, aY, aI, aJ, out, fr, i, r], μ'⟩ ∧
      Answered (Ready31P G X Y aX aY fr) (· < fr) out
        ((WI.zip WJ).map fun q => entryN X Y q.1 q.2) μ i μ')
    WI.length (tQuery31 G D₀ + 20) ?start ?round ?done ?bound
    (hT := by simp [tOffline32P]; ring_nf; omega)
  case start =>
    exact ⟨r, μ₁, by rw [update_frame_setLocal]; rfl, hready, Seg.nil,
      SameOn.mono hblock fun a ha => Or.inl ha.2⟩
  case bound =>
    rintro i _ - - ⟨r, μ', rfl, -⟩
    simp
  case done =>
    rintro _ - ⟨r, μ', rfl, hinv⟩
    rw [← hzip, ← List.length_map (as := WI.zip WJ) fun q => entryN X Y q.1 q.2] at hinv
    refine ⟨hinv.all, fun a ha hoff => hinv.same a ⟨?_, ha⟩⟩
    simpa [hlen] using hoff
  case round =>
    rintro i _ hi - ⟨r, μ', rfl, hinv⟩
    refine (offlineAsk32P_ends hq hg hin (by omega) hi r hinv).mono le_rfl ?_
    rintro _ ⟨r', μ'', rfl, hinv'⟩
    exact ⟨by simp, r', μ'', by rw [update_frame_setLocal]; rfl, hinv'⟩

end Light.Sec4
