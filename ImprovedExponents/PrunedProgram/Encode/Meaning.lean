module

public import ThreeSumApsp.Programs.Sec2.Theorem5.Encode.Meaning
public import ImprovedExponents.PrunedProgram.Encode.Recursion
import all ThreeSumApsp.Programs.Sec2.Theorem5.Encode.Meaning

@[expose] public section

/-!
# What the pruned encoder computes, in the paper's terms

Upstream's `encode_str` (`ThreeSumApsp/Programs/Sec2/Theorem5/Encode/Meaning.lean`) links the
recursion on positions (`encIdx`) with the procedure of Section 2.4.1 (`computeEncoding`): the
output holds the encoding of the array as a full segment.  For the pruned encoder with the budget
`j` the output holds the encoding at the leaves with at most `j` symbols `P₀` (`SegOn j`), within
`cEncP * encWorkP L j` steps (`encodeP_str`).  The link between positions and leaves is upstream's
`encIdx_eq_computeEncoding`, the specification of `encodeP` on positions is `encodeP_spec`.

Adapted from upstream `ThreeSumApsp/Programs/Sec2/Theorem5/Encode/Meaning.lean` (Apache-2.0).
-/

open ThreeSumApsp

namespace Light.Sec2

open Finset ThreeSumApsp.Spec ImprovedExponents

open private encIdx_eq_computeEncoding EncodePre.of_seg
  from ThreeSumApsp.Programs.Sec2.Theorem5.Encode.Meaning

variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ} {src out scr tab p7 p10 L j : ℕ}
  {V : ℤ}

/-- **The encoding of an array on strings at the leaves with few symbols `P₀`** (Section 2.4.1),
for both alphabets at once.  If the source holds the array A on the strings of length L, the table
holds the coefficients, the tables of powers are in their places and the numbers obey the bounds,
then encodeP with the budget `j` ends within `cEncP · encWorkP L j` steps, the output holds what the
procedure of Section 2.4.1 computes at every leaf with at most `j` symbols `P₀`, and only the
output and the scratch area have changed. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/Encode/Meaning.lean (encode_str)
theorem encodeP_str {α : Type} [Fintype α] (e : α ≃ Fin 7) (coef : Term → α → ℤ) {T : List ℤ}
    (hT : T.length = 70) (hc : ∀ x ∈ T, -1 ≤ x ∧ x ≤ 1)
    (hcoef : ∀ lam s, T.getD (7 * (termIdx lam : ℕ) + (e s : ℕ)) 0 = coef lam s) {pS pE : ℕ}
    (hS : P[pS]? = some encStepBody) (hE : P[pE]? = some (encodePBody pS pE))
    (lay : EncodeLayout lim src out scr tab p7 p10 L) (A : (Fin L → α) → ℤ)
    (hsrc : Seg μ src (arrStr e A)) (hV : ∀ u, |A u| ≤ V) (htab : Seg μ tab T)
    (h7 : ∀ i < L, μ (p7 + i) = ((7 ^ i : ℕ) : ℤ)) (h10 : ∀ i < L, μ (p10 + i) = ((10 ^ i : ℕ) : ℤ))
    (hVB : ((7 ^ L : ℕ) : ℤ) * V ≤ lim.word) (hd : d + L ≤ lim.depth) (hj : (j : ℤ) ≤ lim.word) :
    Ends lim P d (encodePBody pS pE) ⟨frame [L, j, src, out, scr, tab, p7, p10], μ⟩
      (cEncP * encWorkP L j) fun σ' => SegOn j σ'.mem out (computeEncoding coef L A) ∧
        SameOutside2 μ σ'.mem out (10 ^ L) scr (scrSize L) := by
  have hbound : ∀ x ∈ arrStr e A, -V ≤ x ∧ x ≤ V := fun x hx => by
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx
    exact abs_le.1 (hV _)
  have pre := EncodePre.of_seg lay (length_arrStr e A) hsrc hbound hT htab hc h7 h10 hVB
  refine (encodeP_spec hS hE hd hj pre).mono (tEncP_le L j) fun σ' h => ⟨?_, h.2⟩
  intro τ hτ
  rw [h.1 τ hτ,
    encIdx_eq_computeEncoding e coef hcoef L A (fun i hi => getD_arrStr_of_lt e A hi) (codeT_lt τ)]
  congr 1
  exact decodeStr_codeStr termEquiv τ

end Light.Sec2
