module

public import ImprovedExponents.Cost8X.Dominated
public import ImprovedExponents.Optimum.PerCBasic
public import ImprovedExponents.Pipeline.Fits
public import ImprovedExponents.PrunedEncoding.Pruned
import all ThreeSumApsp.Sec4.Corollary31

@[expose] public section

/-!
# The cost of the method with pruned encodings

The second summand `N 10^L/(√K N₀)` of the paper's expression (8) (and of `cost8X`) is the cost of
encoding the input arrays of the `≈ N/(√K N₀)` bands: all `10^L` leaves for each band. The pruned
Yates recursion of `ImprovedExponents.PrunedEncoding.Pruned` computes the entries that the method
reads with at most `(27/2) M/(1 - ρ)` multiplications (`prunedMults_le_M`), each with `L` index
operations. This gives the preprocessing cost

  `cost8P L m t N := L m tailX(L, m, t) N² + N L (27/2) M/(1 - ρ)/(√K N₀)`,

whose second summand is `(27/2) N L √K N₀/(1 - ρ)`, as `M = (√K N₀)²` (`encodingP_eq`).

With `L = ⌈cm⌉`, `√K N₀ ≤ e^{m A(L/m)}` for `A(c) = (c/2) H(1/c) + (c - 1) ln 3` (`basePruned`).
So `D^γ L √K N₀ ≤ N` for all large `m` as soon as `ε < R'_c(γ) = ln 4/(A(c) + γ ln 4)` (`RcP`,
`eq_10P`); this takes the place of the paper's inequality (10), which needs `ε < R_c(γ)`.
`costsP` is the analogue of `costsX` with `cost8P` and `R'_c`. The new bound is weaker than the
paper's: `R_c(γ) ≤ R'_c(γ)` (`Rc_le_RcP`), because `A(c) ≤ ln Λ` at `γ = 0`
(`basePruned_le_baseFull`), which is the limit form of `M ≤ 10^L`.
-/

namespace ImprovedExponents

open ThreeSumApsp Real Finset

open private levelsOf_le from ThreeSumApsp.Sec4.Corollary31

/-! ### The cost -/

/-- The preprocessing cost with pruned encodings:
`L m tailX(L, m, t) N² + N L (27/2) M/(1 - ρ)/(√K N₀)`. The first summand is that of `cost8X`;
the second has the `(27/2) M/(1 - ρ)` multiplications of the pruned recursion, with `L` index
operations each, in the place of the `10^L` leaves of a band. -/
noncomputable def cost8P (L m t N : ℕ) : ℝ :=
  (L : ℝ) * (m : ℝ) * tailX L m t * (N : ℝ) ^ 2
    + (N : ℝ) * (L : ℝ) * (27 / 2 * (M L m : ℝ) / (1 - rho L m)) / sqrtKN0 L m

/-- The second summand of `cost8P` is `(27/2) N L √K N₀/(1 - ρ)`, because `M = (√K N₀)²`. -/
theorem encodingP_eq {L m : ℕ} (hmL : m ≤ L) (N : ℕ) :
    (N : ℝ) * (L : ℝ) * (27 / 2 * (M L m : ℝ) / (1 - rho L m)) / sqrtKN0 L m
      = 27 / 2 * (N : ℝ) * ((L : ℝ) * sqrtKN0 L m) / (1 - rho L m) := by
  have hs := (sqrtKN0_pos hmL).ne'
  have h : sqrtKN0 L m ^ 2 * (sqrtKN0 L m)⁻¹ = sqrtKN0 L m := by field_simp
  rw [← sqrtKN0_sq]
  simp only [div_eq_mul_inv]
  linear_combination ((N : ℝ) * (L : ℝ) * (27 / 2) * (1 - rho L m)⁻¹) * h

/-- The second summand of `cost8P` bounds the cost of the pruned recursion on all bands: `L` index
operations for each of its `prunedMults L m` multiplications, for `N/(√K N₀)` bands. -/
theorem prunedMults_cost_le {L m : ℕ} (hL : 10 * m ≤ L) (N : ℕ) :
    (N : ℝ) * (L : ℝ) * (prunedMults L m : ℝ) / sqrtKN0 L m
      ≤ (N : ℝ) * (L : ℝ) * (27 / 2 * (M L m : ℝ) / (1 - rho L m)) / sqrtKN0 L m :=
  div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (prunedMults_le_M hL) (by positivity))
    (sqrtKN0_pos (by omega)).le

/-! ### The two thinness bounds -/

/-- Gibbs' inequality at the weights `1/10` and `9/10`: `H(x) + (1 - x) ln 9 ≤ ln 10`. -/
theorem entropy_add_le_log_ten {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    entropy x + (1 - x) * log 9 ≤ log 10 := by
  have h1x : 0 < 1 - x := sub_pos.2 hx1
  have ha := log_le_sub_one_of_pos (show 0 < 1 / (10 * x) by positivity)
  have hb := log_le_sub_one_of_pos (show 0 < 9 / (10 * (1 - x)) by positivity)
  rw [log_div one_ne_zero (by positivity), log_one, log_mul (by norm_num) hx0.ne'] at ha
  rw [log_div (by norm_num) (by positivity), log_mul (by norm_num) h1x.ne'] at hb
  have ha' := mul_le_mul_of_nonneg_left ha hx0.le
  have hb' := mul_le_mul_of_nonneg_left hb h1x.le
  have e1 : x * (1 / (10 * x) - 1) = 1 / 10 - x := by field_simp
  have e2 : (1 - x) * (9 / (10 * (1 - x)) - 1) = 9 / 10 - (1 - x) := by field_simp
  rw [e1] at ha'
  rw [e2] at hb'
  unfold entropy
  linarith

/-- `A(c) ≤ ln Λ` at `γ = 0`: the constant of the thinness bound with pruned encodings is at most
that of the paper. This is `binom(L, m) 9^{L-m} ≤ 10^L` in the limit. -/
theorem basePruned_le_baseFull {c : ℝ} (hc : 1 < c) : basePruned c ≤ baseFull c := by
  have hc0 : 0 < c := by linarith
  have h := entropy_add_le_log_ten (x := 1 / c) (by positivity) ((div_lt_one hc0).2 hc)
  have h' := mul_le_mul_of_nonneg_left h hc0.le
  have e : c * (1 - 1 / c) = c - 1 := by field_simp
  have hlog : log 9 = 2 * log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, log_pow]
    norm_num
  unfold basePruned baseFull lnΛ
  linear_combination h' - log 9 * e - (c - 1) * hlog

/-- **The thinness bound with pruned encodings is the weaker one**: `R_c(γ) ≤ R'_c(γ)` for
`c ≥ 10` and `γ ≥ 0`. -/
theorem Rc_le_RcP {c γ : ℝ} (hc : 10 ≤ c) (hγ : 0 ≤ γ) : Rc c γ ≤ RcP c γ := by
  rw [Rc_eq_thinR]
  exact thinR_antitone_left (basePruned_pos (by linarith)) (basePruned_le_baseFull (by linarith))
    hγ

/-! ### The encodings fit: the analogue of inequality (10) -/

/-- The analogue of inequality (10) for pruned encodings: `D^γ · L √K N₀ ≤ N` at `L = ⌈cm⌉`, for
every exponent `γ ≥ 0` and `0 < ε < R'_c(γ)`, once `m` exceeds a constant. Here `D₀` is the
original inner dimension with `4^{m-1} < D₀ ≤ N^ε`, and `D` is the padded `4^m`. -/
theorem eq_10P {c γ ε : ℝ} (hc : 10 < c) (hγ : 0 ≤ γ) (hε0 : 0 < ε) (hε : ε < RcP c γ) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ D₀ N : ℕ, 4 ^ (m - 1) < D₀ → (D₀ : ℝ) ≤ (N : ℝ) ^ ε →
      (D m : ℝ) ^ γ * ((levelsOf c m : ℝ) * sqrtKN0 (levelsOf c m) m) ≤ (N : ℝ) := by
  have hlog4 := log_four_pos
  have hA : 0 < basePruned c := basePruned_pos (by linarith)
  have hden : 0 < basePruned c + γ * log 4 := thinR_den_pos hA hγ
  have hε' : ε < log 4 / (basePruned c + γ * log 4) := hε
  -- `ε < R'_c(γ)` says that `A(c) + γ ln 4 < ln 4/ε =: G`
  set G : ℝ := log 4 / ε with hGdef
  have hG : basePruned c + γ * log 4 < G := by
    rw [hGdef, lt_div_iff₀ hε0]
    have := (lt_div_iff₀ hden).1 hε'
    linarith
  -- a constant `B > A(c)` with `B + γ ln 4 < G`, and the room `η` that is left
  set B : ℝ := (basePruned c + (G - γ * log 4)) / 2 with hBdef
  have hB1 : basePruned c < B := by rw [hBdef]; linarith
  set η : ℝ := G - γ * log 4 - B with hηdef
  have hη : 0 < η := by rw [hηdef, hBdef]; linarith
  -- near `c` the constant stays below `B`
  have hcont : ContinuousAt basePruned c :=
    basePruned_continuousOn.continuousAt (Ioi_mem_nhds hc)
  obtain ⟨δ₀, hδ₀, hnear⟩ := Metric.eventually_nhds_iff.1
    (hcont.eventually (gt_mem_nhds hB1))
  refine ⟨max 1 (max ⌈1 / δ₀⌉₊ ⌈2 * (c + 1) * exp G / η ^ 2⌉₊),
    fun m hm D₀ N hgt hthin => ?_⟩
  have hm1 : 1 ≤ m := (le_max_left _ _).trans hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hmδ : 1 / δ₀ ≤ (m : ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_left _ _).trans ((le_max_right _ _).trans hm))
  have hmη : 2 * (c + 1) * exp G / η ^ 2 ≤ (m : ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_right _ _).trans ((le_max_right _ _).trans hm))
  -- the levels: `c ≤ L/m < c + δ₀`
  -- adapted from `ImprovedExponents/Pipeline/Fits.lean` (`exists_fits18`)
  have hLge : c * m ≤ (levelsOf c m : ℝ) := Nat.le_ceil _
  have hLlt : (levelsOf c m : ℝ) < c * m + 1 := Nat.ceil_lt_add_one (by positivity)
  have hmL : m < levelsOf c m := by
    have h : (m : ℝ) < (levelsOf c m : ℝ) := by nlinarith
    exact_mod_cast h
  have hratio1 : c ≤ (levelsOf c m : ℝ) / m := by rwa [le_div_iff₀ hm0]
  have hratio2 : (levelsOf c m : ℝ) / m < c + δ₀ := by
    rw [div_lt_iff₀ hm0]
    have : 1 ≤ δ₀ * m := by
      have := (div_le_iff₀ hδ₀).1 hmδ
      linarith
    nlinarith
  have hbase : basePruned ((levelsOf c m : ℝ) / m) < B := by
    refine hnear ?_
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  have hLle : (levelsOf c m : ℝ) ≤ (c + 1) * m := levelsOf_le hc hm1
  have hsqrt : sqrtKN0 (levelsOf c m) m ≤ exp ((m : ℝ) * B) :=
    (sqrtKN0_le_exp hm1 hmL).trans (exp_le_exp.2 (mul_le_mul_of_nonneg_left hbase.le hm0.le))
  -- `N ≥ 4^{(m-1)/ε} = e^{(m-1) G}`
  have hN : exp (((m : ℝ) - 1) * G) ≤ (N : ℝ) := by
    have h := Corollary31.hypothesis hm1 hε0 hgt hthin
    rwa [rpow_def_of_pos (by norm_num),
      show log 4 * (((m : ℝ) - 1) / ε) = ((m : ℝ) - 1) * (log 4 / ε) by ring] at h
  -- the room `η` pays for the factor `L ≤ (c + 1) m` and for `e^G`
  have hexp : (c + 1) * m * exp G ≤ exp ((m : ℝ) * η) := by
    have hq := quadratic_le_exp_of_nonneg (mul_nonneg hm0.le hη.le)
    have h1 : 2 * (c + 1) * exp G ≤ (m : ℝ) * η ^ 2 := by
      have := (div_le_iff₀ (pow_pos hη 2)).1 hmη
      linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hm0.le
    have h3 : 0 ≤ (m : ℝ) * η := mul_nonneg hm0.le hη.le
    linarith
  have hE : exp (γ * ((m : ℝ) * log 4)) * exp ((m : ℝ) * B)
      = exp G * exp ((m : ℝ) * (B + γ * log 4) - G) := by
    rw [← exp_add, ← exp_add]
    congr 1
    ring
  calc (D m : ℝ) ^ γ * ((levelsOf c m : ℝ) * sqrtKN0 (levelsOf c m) m)
      ≤ exp (γ * ((m : ℝ) * log 4)) * ((c + 1) * m * exp ((m : ℝ) * B)) := by
        rw [cast_D_rpow]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul hLle hsqrt (sqrtKN0_pos hmL.le).le (by positivity)) (exp_pos _).le
    _ = (c + 1) * m * (exp (γ * ((m : ℝ) * log 4)) * exp ((m : ℝ) * B)) := by ring
    _ = (c + 1) * m * exp G * exp ((m : ℝ) * (B + γ * log 4) - G) := by
        rw [hE]
        ring
    _ ≤ exp ((m : ℝ) * η) * exp ((m : ℝ) * (B + γ * log 4) - G) :=
        mul_le_mul_of_nonneg_right hexp (exp_pos _).le
    _ = exp (((m : ℝ) - 1) * G) := by
        rw [← exp_add, hηdef]
        congr 1
        ring
    _ ≤ (N : ℝ) := hN

/-! ### The two terms together -/

/-- `cost8P` is `O(N² log² D/D^γ)`, in the given `D`, wherever `D^γ L √K N₀ ≤ N` holds with the
exponent `γ < γX(c, θ)`. This takes the place of `dominated_cost8X`. -/
theorem dominated_cost8P {c θ γ : ℝ} (hc : 10 < c) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hγ : γ < gammaX c θ) {dom : Sizes → Prop} (hset : ∀ p, dom p → p.SetUp)
    (h10 : ∀ p, dom p →
      (D p.m : ℝ) ^ γ * ((levelsOf c p.m : ℝ) * sqrtKN0 (levelsOf c p.m) p.m) ≤ p.N) :
    Dominated dom (fun p => cost8P (levelsOf c p.m) p.m (switchOf θ p.m) p.N)
      fun p => (p.N : ℝ) ^ 2 * Real.log p.D₀ ^ 2 / (p.D₀ : ℝ) ^ γ := by
  have hρ : rhoC c < 1 := rhoC_lt_one hc
  -- the first term, with its factor `N²`
  have hboxes : Dominated dom
      (fun p => (levelsOf c p.m : ℝ) * p.m * tailX (levelsOf c p.m) p.m (switchOf θ p.m)
        * (p.N : ℝ) ^ 2)
      fun p => (D p.m : ℝ) ^ (-γ) * Real.log (D p.m) ^ 2 * (p.N : ℝ) ^ 2 :=
    ((first_termX hc hθ0 hθ1 hγ).comp Sizes.m fun p hp => (hset p hp).m_pos).mul_right
      (k := fun p => (p.N : ℝ) ^ 2) fun _ _ => sq_nonneg _
  -- the encodings
  have hencodings : Dominated dom
      (fun p => (p.N : ℝ) * (levelsOf c p.m : ℝ)
        * (27 / 2 * (M (levelsOf c p.m) p.m : ℝ) / (1 - rho (levelsOf c p.m) p.m))
        / sqrtKN0 (levelsOf c p.m) p.m)
      fun p => (D p.m : ℝ) ^ (-γ) * Real.log (D p.m) ^ 2 * (p.N : ℝ) ^ 2 := by
    refine .of_le_const_mul (C := 27 / 2 / (1 - rhoC c))
      (div_nonneg (by norm_num) (sub_pos.2 hρ).le) fun p hp => ?_
    have hm1 : 1 ≤ p.m := (hset p hp).m_pos
    have hmL : p.m ≤ levelsOf c p.m := by have := ten_mul_le_levelsOf hc p.m; omega
    have hrho : rho (levelsOf c p.m) p.m < rhoC c := Corollary31.rho_lt hc p.m
    have hDγ : 0 < (D p.m : ℝ) ^ γ := rpow_pos_of_pos (cast_D_pos p.m) γ
    have hLs0 : 0 ≤ (levelsOf c p.m : ℝ) * sqrtKN0 (levelsOf c p.m) p.m :=
      mul_nonneg (Nat.cast_nonneg _) (sqrtKN0_pos hmL).le
    have hLs : (levelsOf c p.m : ℝ) * sqrtKN0 (levelsOf c p.m) p.m
        ≤ (D p.m : ℝ) ^ (-γ) * p.N := by
      rw [rpow_neg (cast_D_pos p.m).le, inv_mul_eq_div, le_div_iff₀ hDγ, mul_comm]
      exact h10 p hp
    have hlog : (1 : ℝ) ≤ Real.log (D p.m) ^ 2 :=
      one_le_pow₀ ((Nat.one_le_cast.2 hm1).trans (cast_le_log_cast_D p.m))
    have hpow : (0 : ℝ) ≤ (D p.m : ℝ) ^ (-γ) := rpow_nonneg (Nat.cast_nonneg _) _
    rw [encodingP_eq hmL]
    calc 27 / 2 * (p.N : ℝ) * ((levelsOf c p.m : ℝ) * sqrtKN0 (levelsOf c p.m) p.m)
          / (1 - rho (levelsOf c p.m) p.m)
        ≤ 27 / 2 * (p.N : ℝ) * ((levelsOf c p.m : ℝ) * sqrtKN0 (levelsOf c p.m) p.m)
          / (1 - rhoC c) :=
          div_le_div_of_nonneg_left (mul_nonneg (by positivity) hLs0) (sub_pos.2 hρ)
            (by linarith)
      _ ≤ 27 / 2 * (p.N : ℝ) * ((D p.m : ℝ) ^ (-γ) * p.N) / (1 - rhoC c) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hLs (by positivity))
            (sub_pos.2 hρ).le
      _ = 27 / 2 / (1 - rhoC c) * ((D p.m : ℝ) ^ (-γ) * 1 * (p.N : ℝ) ^ 2) := by ring
      _ ≤ 27 / 2 / (1 - rhoC c)
            * ((D p.m : ℝ) ^ (-γ) * Real.log (D p.m) ^ 2 * (p.N : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hlog hpow) (sq_nonneg _))
            (div_nonneg (by norm_num) (sub_pos.2 hρ).le)
  have hpadded : Dominated dom (fun p => cost8P (levelsOf c p.m) p.m (switchOf θ p.m) p.N)
      fun p => (D p.m : ℝ) ^ (-γ) * Real.log (D p.m) ^ 2 * (p.N : ℝ) ^ 2 :=
    hboxes.add hencodings
  refine (hpadded.trans (((padded_le (-γ) 2).mono_dom hset).mul_right
    fun _ _ => sq_nonneg _)).congr (fun _ _ => rfl) fun p _ => ?_
  rw [Real.rpow_neg (Nat.cast_nonneg _)]
  ring

/-- **The cost bounds with pruned encodings**, for all large `m`. For `c > 10`, `0 < θ < 0.9`,
`0 ≤ γ < γX(c, θ)` and `0 < ε < R'_c(γ)` there are a constant `C` and a threshold `m₀` such that
for all `2 ≤ D ≤ N^ε` with `m = ⌈log_4 D⌉ ≥ m₀`, `L = ⌈cm⌉`, `t = ⌈θm⌉`: the hypothesis
`N ≥ √K N₀` of Theorem 30 holds, `cost8P` is at most `C N² log² D/D^γ`, and the query cost is at
most `C D^q log D`. This is `costsX` with pruned encodings: `cost8P` in the place of `cost8X` and
the thinness bound `R'_c` in the place of `R_c`. -/
theorem costsP {c θ γ ε : ℝ} (hc : 10 < c) (hθ0 : 0 < θ) (hθ1 : θ < 0.9) (hγ0 : 0 ≤ γ)
    (hγ : γ < gammaX c θ) (hε0 : 0 < ε) (hε : ε < RcP c γ) :
    ∃ (C : ℝ) (m₀ : ℕ), 0 ≤ C ∧ ∀ D₀ N m : ℕ, 2 ≤ D₀ → (D₀ : ℝ) ≤ (N : ℝ) ^ ε →
      m = ⌈Real.logb 4 (D₀ : ℝ)⌉₊ → m₀ ≤ m →
      sqrtKN0 (levelsOf c m) m ≤ N ∧
      cost8P (levelsOf c m) m (switchOf θ m) N
        ≤ C * ((N : ℝ) ^ 2 * Real.log (D₀ : ℝ) ^ 2 / (D₀ : ℝ) ^ γ) ∧
      costQuery (levelsOf c m) m (switchOf θ m) ≤ C * ((D₀ : ℝ) ^ qOf θ * Real.log (D₀ : ℝ)) := by
  obtain ⟨m₀, heq10⟩ := eq_10P hc hγ0 hε0 hε
  -- the encodings fit for the instances from the threshold on
  have h10 : ∀ p : Sizes, p.Corollary31 ε m₀ →
      (D p.m : ℝ) ^ γ * ((levelsOf c p.m : ℝ) * sqrtKN0 (levelsOf c p.m) p.m) ≤ p.N :=
    fun p hp => heq10 p.m hp.large p.D₀ p.N hp.setUp.gt hp.thin
  have hpre := dominated_cost8P hc hθ0.le (by linarith) hγ
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
  have hm1 : 1 ≤ m := hp.setUp.m_pos
  have hL10 : 10 * m ≤ levelsOf c m := ten_mul_le_levelsOf hc m
  -- `√K N₀ ≤ D^γ L √K N₀ ≤ N`
  have hD1 : (1 : ℝ) ≤ (D m : ℝ) ^ γ := Real.one_le_rpow (one_le_cast_D m) hγ0
  have hL1 : (1 : ℝ) ≤ (levelsOf c m : ℝ) := Nat.one_le_cast.2 (by omega)
  have hs : 0 ≤ sqrtKN0 (levelsOf c m) m := (sqrtKN0_pos (by omega)).le
  have hfit : sqrtKN0 (levelsOf c m) m ≤ N :=
    calc sqrtKN0 (levelsOf c m) m
        ≤ (levelsOf c m : ℝ) * sqrtKN0 (levelsOf c m) m := le_mul_of_one_le_left hs hL1
      _ ≤ (D m : ℝ) ^ γ * ((levelsOf c m : ℝ) * sqrtKN0 (levelsOf c m) m) :=
          le_mul_of_one_le_left (mul_nonneg (by positivity) hs) hD1
      _ ≤ N := h10 ⟨D₀, N, m⟩ hp
  exact ⟨hfit, hboth ⟨D₀, N, m⟩ hp⟩

end ImprovedExponents
