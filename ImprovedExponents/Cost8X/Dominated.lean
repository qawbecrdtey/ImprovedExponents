module

public import ThreeSumApsp.Sec4.Corollary31
public import ImprovedExponents.ExactCount.Tail
public import ImprovedExponents.Cost8X.Defs
import all ThreeSumApsp.Sec4.Corollary31

@[expose] public section

/-!
# `cost8X` at the parameters of Corollary 31

With `L = ⌈cm⌉` levels, the switching order `t = ⌈θm⌉` and `D = 4^m`, the tail of the leaf counts
is at most `(m + 1)(L + 1) D^{-γX(c, θ)}` (`sum_beta_le_rpow`), where `γX(c, θ) = -g₂(c, θ)/ln 4`
is the exact exponent. So for every `γ < γX(c, θ)` the first term of `cost8X` is
`O(N² log² D/D^γ)`: the slack `γX - γ` pays for the factor `(m + 1)(L + 1)` (`first_termX`). The
second term is that of the paper's expression (8) and is bounded by its inequality (10), which
holds for every `γ ≥ 0` and `ε < R_c(γ)` (`eq_10X`).

`costsX` puts the two together, in the form of upstream's `ThreeSumApsp.Corollary31.costs`, with
`cost8X` in the place of (8) and any `γ < γX(c, θ)` in the place of `γ = θ ln(1/ρ_c)/ln 4`.
-/

namespace ImprovedExponents

open ThreeSumApsp Real Finset

open private levelsOf_le exists_mul_sqrt_le_pow pos_of_le_rpow from ThreeSumApsp.Sec4.Corollary31

/-! ### The first term -/

/-- The tail at the parameters of Corollary 31: `tailX ≤ (m + 1)(L + 1) D^{-γX(c, θ)}`. -/
theorem tailX_le_rpow {c θ : ℝ} (hc : 10 < c) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) {m : ℕ} (hm : 1 ≤ m) :
    tailX (levelsOf c m) m (switchOf θ m)
      ≤ ((m : ℝ) + 1) * (((levelsOf c m : ℝ) + 1) * (D m : ℝ) ^ (-gammaX c θ)) := by
  have hmL : m ≤ levelsOf c m := by have := ten_mul_le_levelsOf hc m; omega
  have hM : (0 : ℝ) < M (levelsOf c m) m :=
    sqrtKN0_sq (levelsOf c m) m ▸ pow_pos (sqrtKN0_pos hmL) 2
  unfold tailX
  rw [div_le_iff₀ hM]
  exact (sum_beta_le_rpow hc hθ0 hθ1 hm).trans (le_of_eq (by ring))

/-- `m² D^{-δ} ≤ 2/(δ ln 4)²` for `δ > 0` and `D = 4^m`: a power of `D` pays for `log² D`. -/
theorem sq_mul_D_rpow_le {δ : ℝ} (hδ : 0 < δ) (m : ℕ) :
    (m : ℝ) ^ 2 * (D m : ℝ) ^ (-δ) ≤ 2 / (δ * log 4) ^ 2 := by
  have hlog := log_four_pos
  have hx : 0 ≤ δ * ((m : ℝ) * log 4) := by positivity
  have hexp := quadratic_le_exp_of_nonneg hx
  rw [cast_D_rpow, show -δ * ((m : ℝ) * log 4) = -(δ * ((m : ℝ) * log 4)) by ring, exp_neg,
    ← div_eq_mul_inv, div_le_div_iff₀ (exp_pos _) (by positivity)]
  have hsq : (m : ℝ) ^ 2 * (δ * log 4) ^ 2 = (δ * ((m : ℝ) * log 4)) ^ 2 := by ring
  rw [hsq]
  linarith

/-- **The first term of `cost8X`** for general `c` and `θ`, and every `γ` below the exact exponent
`γX(c, θ)`: it is `O(N² log² D/D^γ)`. The common factor `N²` is left out. This takes the place of
`ThreeSumApsp.Corollary31.first_term`. -/
theorem first_termX {c θ γ : ℝ} (hc : 10 < c) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hγ : γ < gammaX c θ) :
    Dominated (fun m : ℕ => 1 ≤ m)
      (fun m => (levelsOf c m : ℝ) * m * tailX (levelsOf c m) m (switchOf θ m))
      fun m => (D m : ℝ) ^ (-γ) * Real.log (D m) ^ 2 := by
  have hc0 : (0 : ℝ) < c := by linarith
  have hδ : 0 < gammaX c θ - γ := sub_pos.2 hγ
  have hlog4 := log_four_pos
  refine .of_le_const_mul (C := 2 * (c + 1) * (c + 2) * (2 / ((gammaX c θ - γ) * log 4) ^ 2))
    (by positivity) fun m hm => ?_
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hL : (levelsOf c m : ℝ) ≤ (c + 1) * m := levelsOf_le hc hm
  have htail := tailX_le_rpow hc hθ0 hθ1 hm
  have hsplit : (D m : ℝ) ^ (-gammaX c θ)
      = (D m : ℝ) ^ (-(gammaX c θ - γ)) * (D m : ℝ) ^ (-γ) := by
    rw [← rpow_add (cast_D_pos m)]
    congr 1
    ring
  have hpow : (0 : ℝ) ≤ (D m : ℝ) ^ (-gammaX c θ) := rpow_nonneg (Nat.cast_nonneg _) _
  have hpow' : (0 : ℝ) ≤ (D m : ℝ) ^ (-γ) := rpow_nonneg (Nat.cast_nonneg _) _
  have hmlog : (m : ℝ) ≤ Real.log (D m) := cast_le_log_cast_D m
  calc (levelsOf c m : ℝ) * m * tailX (levelsOf c m) m (switchOf θ m)
      ≤ (c + 1) * m * m * (((m : ℝ) + 1) * (((levelsOf c m : ℝ) + 1)
          * (D m : ℝ) ^ (-gammaX c θ))) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hL (Nat.cast_nonneg m)) htail
          (tailX_nonneg _ _ _) (by positivity)
    _ ≤ (c + 1) * m * m * ((2 * (m : ℝ)) * (((c + 2) * m) * (D m : ℝ) ^ (-gammaX c θ))) := by
        gcongr <;> linarith
    _ = 2 * (c + 1) * (c + 2) * ((m : ℝ) ^ 2 * (D m : ℝ) ^ (-(gammaX c θ - γ)))
          * ((D m : ℝ) ^ (-γ) * (m : ℝ) ^ 2) := by
        rw [hsplit]
        ring
    _ ≤ 2 * (c + 1) * (c + 2) * (2 / ((gammaX c θ - γ) * log 4) ^ 2)
          * ((D m : ℝ) ^ (-γ) * Real.log (D m) ^ 2) := by
        have h := sq_mul_D_rpow_le hδ m
        gcongr

/-! ### The second term: inequality (10) for every exponent -/

-- adapted from upstream `ThreeSumApsp/Sec4/Corollary31.lean` (`eq_10`), where the exponent is
-- `gammaOf c θ`; the proof uses only that it is not negative
/-- Inequality (10), `D^γ · 10^L/(√K N₀) ≤ N`, at `L = ⌈cm⌉`, for every exponent `γ ≥ 0` and
`ε < R_c(γ)`, once `m` exceeds a constant: `D₀` is the original inner dimension with
`4^{m-1} < D₀ ≤ N^ε`, and the `D` of (10) is the padded `4^m`. -/
theorem eq_10X (c γ ε : ℝ) (hc : 10 < c) (hγ : 0 ≤ γ) (hε : ε < Rc c γ) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ D₀ N : ℕ, 4 ^ (m - 1) < D₀ → (D₀ : ℝ) ≤ (N : ℝ) ^ ε →
      lhs10 (levelsOf c m) m γ ≤ (N : ℝ) := by
  rcases le_or_gt ε 0 with hε0 | hε0
  · exact ⟨0, fun m _ D₀ N hgt hthin => absurd (pos_of_le_rpow hgt hthin) hε0.not_gt⟩
  obtain ⟨C, hC, hlhs⟩ := Corollary31.lhs10_le hc γ
  -- "As ε < R_c(γ) says that Λ < 4^{1/ε}"
  have hΛ0 : 0 < Real.exp (lnΛ c γ) := Real.exp_pos _
  have hΛ : Real.exp (lnΛ c γ) < (4 : ℝ) ^ (1 / ε) := (eq_11_iff c γ ε hc.le hγ hε0).2 hε
  -- "once m exceeds a constant": `(4^{1/ε}/Λ)^m ≥ C 4^{1/ε} √m`
  obtain ⟨m₀, hm₀⟩ := exists_mul_sqrt_le_pow (A := C * (4 : ℝ) ^ (1 / ε)) (by positivity)
    ((one_lt_div hΛ0).2 hΛ)
  refine ⟨m₀ + 1, fun m hm D₀ N hgt hthin => ?_⟩
  have hpow : (4 : ℝ) ^ (((m : ℝ) - 1) / ε) = ((4 : ℝ) ^ (1 / ε)) ^ m / (4 : ℝ) ^ (1 / ε) := by
    rw [sub_div, Real.rpow_sub (by norm_num), div_eq_mul_one_div (m : ℝ) ε, mul_comm,
      Real.rpow_mul (by norm_num), Real.rpow_natCast]
  calc lhs10 (levelsOf c m) m γ
      ≤ C * (Real.sqrt m * Real.exp (lnΛ c γ) ^ m) := hlhs m (by omega)
    _ = C * (4 : ℝ) ^ (1 / ε) * Real.sqrt m / ((4 : ℝ) ^ (1 / ε) / Real.exp (lnΛ c γ)) ^ m
          * (4 : ℝ) ^ (((m : ℝ) - 1) / ε) := by
        rw [hpow, div_pow]
        field_simp
    _ ≤ 1 * (4 : ℝ) ^ (((m : ℝ) - 1) / ε) := by
        gcongr
        exact (div_le_one (by positivity)).2 (hm₀ m (by omega))
    _ ≤ (N : ℝ) := by
        rw [one_mul]
        exact Corollary31.hypothesis (by omega) hε0 hgt hthin

/-! ### The two terms together -/

/-- `cost8X` from its two terms, with `L` and `t` given as functions of `m`. If the first term,
without its factor `N²`, is `O(G)`, where `G ≥ D^{-γ}`, then `cost8X` is `O(G N²)` wherever (10)
holds. This takes the place of `ThreeSumApsp.dominated_cost8_of_eq_10`. -/
theorem dominated_cost8X_of_eq_10 {Lof tof : ℕ → ℕ} {γ : ℝ} {G : ℕ → ℝ} {domM : ℕ → Prop}
    {dom : Sizes → Prop}
    (hfirst : Dominated domM (fun m => (Lof m : ℝ) * m * tailX (Lof m) m (tof m)) G)
    (hdom : ∀ p, dom p → domM p.m) (hG : ∀ p, dom p → (D p.m : ℝ) ^ (-γ) ≤ G p.m)
    (h10 : ∀ p, dom p → lhs10 (Lof p.m) p.m γ ≤ p.N) :
    Dominated dom (fun p => cost8X (Lof p.m) p.m (tof p.m) p.N)
      fun p => G p.m * (p.N : ℝ) ^ 2 := by
  -- the first term, with its factor `N²`
  have hboxes := (hfirst.comp Sizes.m hdom).mul_right (k := fun p => (p.N : ℝ) ^ 2)
    fun _ _ => sq_nonneg _
  -- the last term
  have hencodings : Dominated dom
      (fun p => (p.N : ℝ) * (10 : ℝ) ^ Lof p.m / sqrtKN0 (Lof p.m) p.m)
      fun p => G p.m * (p.N : ℝ) ^ 2 :=
    .of_le fun p hp => (Equation10.last_term (h10 p hp)).trans <| by
      rw [div_eq_mul_inv, mul_comm, ← Real.rpow_neg (cast_D_pos p.m).le]
      exact mul_le_mul_of_nonneg_right (hG p hp) (sq_nonneg _)
  exact hboxes.add hencodings

/-- `cost8X` is `O(N² log² D/D^γ)`, in the given `D`, wherever (10) holds with the exponent
`γ < γX(c, θ)`. -/
theorem dominated_cost8X {c θ γ : ℝ} (hc : 10 < c) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hγ : γ < gammaX c θ) {dom : Sizes → Prop} (hset : ∀ p, dom p → p.SetUp)
    (h10 : ∀ p, dom p → lhs10 (levelsOf c p.m) p.m γ ≤ p.N) :
    Dominated dom (fun p => cost8X (levelsOf c p.m) p.m (switchOf θ p.m) p.N)
      fun p => (p.N : ℝ) ^ 2 * Real.log p.D₀ ^ 2 / (p.D₀ : ℝ) ^ γ := by
  have hpadded : Dominated dom (fun p => cost8X (levelsOf c p.m) p.m (switchOf θ p.m) p.N)
      fun p => (D p.m : ℝ) ^ (-γ) * Real.log (D p.m) ^ 2 * (p.N : ℝ) ^ 2 :=
    dominated_cost8X_of_eq_10 (Lof := levelsOf c) (tof := switchOf θ)
      (G := fun m => (D m : ℝ) ^ (-γ) * Real.log (D m) ^ 2)
      (first_termX hc hθ0 hθ1 hγ) (fun p hp => (hset p hp).m_pos)
      (fun p hp => le_mul_of_one_le_right (by positivity) (one_le_pow₀
        ((Nat.one_le_cast.2 (hset p hp).m_pos).trans (cast_le_log_cast_D p.m)))) h10
  refine (hpadded.trans (((padded_le (-γ) 2).mono_dom hset).mul_right
    fun _ _ => sq_nonneg _)).congr (fun _ _ => rfl) fun p _ => ?_
  rw [Real.rpow_neg (Nat.cast_nonneg _)]
  ring

/-- **The cost bounds with the exact exponent**, for all large `m`. For `c > 10`, `0 < θ < 0.9`,
`0 ≤ γ < γX(c, θ)` and `ε < R_c(γ)` there are a constant `C` and a threshold `m₀` such that for
all `2 ≤ D ≤ N^ε` with `m = ⌈log_4 D⌉ ≥ m₀`, `L = ⌈cm⌉`, `t = ⌈θm⌉`: the hypothesis `N ≥ √K N₀`
of Theorem 30 holds, `cost8X` is at most `C N² log² D/D^γ`, and the query cost is at most
`C D^q log D`. This takes the place of `ThreeSumApsp.Corollary31.costs`. -/
theorem costsX {c θ γ ε : ℝ} (hc : 10 < c) (hθ0 : 0 < θ) (hθ1 : θ < 0.9) (hγ0 : 0 ≤ γ)
    (hγ : γ < gammaX c θ) (hε : ε < Rc c γ) :
    ∃ (C : ℝ) (m₀ : ℕ), 0 ≤ C ∧ ∀ D₀ N m : ℕ, 2 ≤ D₀ → (D₀ : ℝ) ≤ (N : ℝ) ^ ε →
      m = ⌈Real.logb 4 (D₀ : ℝ)⌉₊ → m₀ ≤ m →
      sqrtKN0 (levelsOf c m) m ≤ N ∧
      cost8X (levelsOf c m) m (switchOf θ m) N
        ≤ C * ((N : ℝ) ^ 2 * Real.log (D₀ : ℝ) ^ 2 / (D₀ : ℝ) ^ γ) ∧
      costQuery (levelsOf c m) m (switchOf θ m) ≤ C * ((D₀ : ℝ) ^ qOf θ * Real.log (D₀ : ℝ)) := by
  obtain ⟨m₀, heq10⟩ := eq_10X c γ ε hc hγ0 hε
  -- (10) holds for the instances from the threshold on
  have h10 : ∀ p : Sizes, p.Corollary31 ε m₀ → lhs10 (levelsOf c p.m) p.m γ ≤ p.N :=
    fun p hp => heq10 p.m hp.large p.D₀ p.N hp.setUp.gt hp.thin
  have hpre := dominated_cost8X hc hθ0.le (by linarith) hγ
    (fun p (hp : p.Corollary31 ε m₀) => hp.setUp) h10
  have hquery : Dominated (Sizes.Corollary31 ε m₀)
      (fun p => costQuery (levelsOf c p.m) p.m (switchOf θ p.m))
      fun p => (p.D₀ : ℝ) ^ qOf θ * Real.log p.D₀ :=
    (((Corollary31.query_cost hc hθ0 hθ1).comp Sizes.m fun _ (hp : Sizes.SetUp _) => hp.m_pos).trans
      (by simpa only [pow_one] using padded_le (qOf θ) 1)).mono_dom fun p hp => hp.setUp
  obtain ⟨C, hC, hboth⟩ := hpre.exists_const_and hquery
    (fun p _ => div_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    fun p hp => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (Real.log_nonneg (Nat.one_le_cast.2 (one_le_two.trans hp.setUp.two_le)))
  refine ⟨C, m₀, hC, fun D₀ N m hD hDN hm hm₀ => ?_⟩
  have hp : Sizes.Corollary31 ε m₀ ⟨D₀, N, m⟩ := ⟨⟨hD, hm⟩, hDN, hm₀⟩
  have hmL : m ≤ levelsOf c m := by have := ten_mul_le_levelsOf hc m; omega
  exact ⟨Equation10.tile_fits hmL hγ0 (h10 ⟨D₀, N, m⟩ hp), hboth ⟨D₀, N, m⟩ hp⟩

end ImprovedExponents
