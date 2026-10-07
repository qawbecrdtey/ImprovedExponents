module

public import ImprovedExponents.AllEdges.Task
public import ImprovedExponents.AllEdges.Pairs.Passes
public import ImprovedExponents.MinPlus.ExactTriangle
public import ThreeSumApsp.Spec.Sec3.Theorem21b.NegativeTriangle
public import ThreeSumApsp.Programs.Sec3.Theorem21b.MinPlus.Tasks

@[expose] public section

/-!
# The questions of the reduction from all pairs to all-edges Exact Triangle

Footnote 10 of the paper: the (min,+)-product reduces to the all-edges version of Exact Triangle
on the same `n` vertices.  The step from the threshold questions of upstream's `pairsTask`
("is there a `k` with `X[i,k] + Y[k,j] < V[i,j]`?") to zero triangles is Lemma F of the paper
(`ImprovedExponents.add_lt_iff_shiftDiff`, in the form `exists_lt_iff_exists_exactTriangle`): with
`b = aeLevels U` levels, `3U < 2^b ≤ 6U`, the threshold holds for some `k` if and only if one of
the `2b + 3` instances `(ℓ, r) ∈ lemmaFInstances b` has a zero triangle through `(i, j)`.

The instance `(ℓ, r)` has, in the convention of `aeTask` (`AB` at `a n + b`, `BC` at `b n + c`,
`AC` at `a n + c`, with `a = i`, `b = j`, `c = k`), the matrices `r − ⌊(V + 2U)/2^ℓ⌋` (`instAB`),
the transpose of `⌊(Y + U)/2^ℓ⌋` (`instBC`) and `⌊(X + U)/2^ℓ⌋` (`instAC`).  `pairFlags_iff`
is the bridge, `absLe_inst*` bound the weights by `9U`, and `orFlags` with `orL_orFlags` describes
the disjunction of the flags of the instances asked so far.
-/

namespace ImprovedExponents.AllEdges

open Light Light.Sec3 ThreeSumApsp ThreeSumApsp.Spec

/-- The number of levels: for `U ≥ 1`, the least `b` with `2^b > 3U`. -/
def aeLevels (U : ℕ) : ℕ := Nat.log 2 (3 * U) + 1

theorem lt_two_pow_aeLevels (U : ℕ) : 3 * U < 2 ^ aeLevels U :=
  Nat.lt_pow_succ_log_self (by norm_num) _

theorem two_pow_aeLevels_le {U : ℕ} (hU : 1 ≤ U) : 2 ^ aeLevels U ≤ 6 * U := by
  have := Nat.pow_log_le_self 2 (show 3 * U ≠ 0 by omega)
  rw [aeLevels, pow_succ]
  omega

/-! ## The lists of the instances -/

/-- The shifted numbers at the start: `X + U`, the transpose of `Y` plus `U`, and `V + 2U`, one
list after the other (the array on which the prefixes are computed). -/
def pStart (n U : ℕ) (X Y V : List ℤ) : List ℤ :=
  affL 1 U X ++ (transposeL n U Y ++ affL 1 (2 * U) V)

/-- The matrix `AC` of the instance of the level `ℓ`: `⌊(X + U)/2^ℓ⌋`. -/
def instAC (U : ℕ) (X : List ℤ) (ℓ : ℕ) : List ℤ := (affL 1 U X).map (prefQ ℓ)

/-- The matrix `BC` of the instance of the level `ℓ`: the transpose of `⌊(Y + U)/2^ℓ⌋`. -/
def instBC (n U : ℕ) (Y : List ℤ) (ℓ : ℕ) : List ℤ := (transposeL n U Y).map (prefQ ℓ)

/-- The matrix `AB` of the instance `(ℓ, r)`: `r − ⌊(V + 2U)/2^ℓ⌋`. -/
def instAB (U : ℕ) (V : List ℤ) (ℓ : ℕ) (r : ℤ) : List ℤ :=
  affL (-1) r ((affL 1 (2 * U) V).map (prefQ ℓ))

section Lists

variable {n U : ℕ} {X Y V : List ℤ}

theorem length_pStart (hX : X.length = n * n) (hV : V.length = n * n) :
    (pStart n U X Y V).length = 3 * (n * n) := by
  simp only [pStart, List.length_append, length_affL, length_transposeL, hX, hV]
  omega

/-- The numbers at the start are between `0` and `3U`. -/
theorem pStart_range (hX : AbsLe X U) (hY : AbsLe Y U) (hV : AbsLe V U) (hlenY : Y.length = n * n) :
    ∀ z ∈ pStart n U X Y V, 0 ≤ z ∧ z ≤ 3 * (U : ℤ) := by
  intro z hz
  simp only [pStart, List.mem_append] at hz
  rcases hz with hz | hz | hz
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hz
    have := abs_le.1 (hX x hx)
    constructor <;> omega
  · have := mem_transposeL_bounds hY hlenY U z hz
    constructor <;> omega
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hz
    have := abs_le.1 (hV x hx)
    constructor <;> omega

/-- The entry `idx` of a mapped list. -/
theorem getD_map_of_lt (f : ℤ → ℤ) {l : List ℤ} {idx : ℕ} (h : idx < l.length) :
    (l.map f).getD idx 0 = f (l.getD idx 0) := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getD_eq_getElem _ _ h, List.getElem_map]

/-- The entries of the prefixes of a list of numbers in `[0, B]` lie in `[0, B]`. -/
theorem absLe_map_prefQ {l : List ℤ} {B : ℤ} (h : ∀ z ∈ l, 0 ≤ z ∧ z ≤ B) (ℓ : ℕ) :
    ∀ z ∈ l.map (prefQ ℓ), 0 ≤ z ∧ z ≤ B := by
  intro z hz
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hz
  exact ⟨prefQ_nonneg (h y hy).1 ℓ, (prefQ_le (h y hy).1 ℓ).trans (h y hy).2⟩

/-- The parts of the prefixes of the start list. -/
theorem absLe_pStart_parts (hX : AbsLe X U) (hY : AbsLe Y U) (hV : AbsLe V U)
    (hlenY : Y.length = n * n) (ℓ : ℕ) :
    (∀ z ∈ instAC U X ℓ, 0 ≤ z ∧ z ≤ 3 * (U : ℤ)) ∧
      (∀ z ∈ instBC n U Y ℓ, 0 ≤ z ∧ z ≤ 3 * (U : ℤ)) ∧
      ∀ z ∈ (affL 1 (2 * U) V).map (prefQ ℓ), 0 ≤ z ∧ z ≤ 3 * (U : ℤ) := by
  have h := absLe_map_prefQ (pStart_range hX hY hV hlenY) ℓ
  simp only [pStart, List.map_append, List.mem_append] at h
  exact ⟨fun z hz => h z (Or.inl hz), fun z hz => h z (Or.inr (Or.inl hz)),
    fun z hz => h z (Or.inr (Or.inr hz))⟩

/-- The weights of the three matrices of an instance are bounded by `9U`. -/
theorem absLe_inst (hX : AbsLe X U) (hY : AbsLe Y U) (hV : AbsLe V U) (hlenY : Y.length = n * n)
    (hU : 1 ≤ U) {ℓ : ℕ} {r : ℤ} (hr : 1 ≤ r ∧ r ≤ 3) :
    AbsLe (instAB U V ℓ r) ((9 * U : ℕ) : ℤ) ∧ AbsLe (instBC n U Y ℓ) ((9 * U : ℕ) : ℤ) ∧
      AbsLe (instAC U X ℓ) ((9 * U : ℕ) : ℤ) := by
  obtain ⟨h1, h2, h3⟩ := absLe_pStart_parts hX hY hV hlenY ℓ
  push_cast
  refine ⟨fun z hz => ?_, fun z hz => ?_, fun z hz => ?_⟩
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hz
    have := h3 y hy
    exact abs_le.2 ⟨by omega, by omega⟩
  · have := h2 z hz
    exact abs_le.2 ⟨by omega, by omega⟩
  · have := h1 z hz
    exact abs_le.2 ⟨by omega, by omega⟩

/-! ## The bridge -/

/-- **The bridge**: the flag of the pair `q` of `pairsTask` is 1 if and only if one of the
instances `(ℓ, r) ∈ lemmaFInstances (aeLevels U)` has the flag 1 at `q`. -/
theorem pairFlags_iff (hX : AbsLe X U) (hY : AbsLe Y U) (hV : AbsLe V U)
    (hlX : X.length = n * n) (hlY : Y.length = n * n) (hlV : V.length = n * n) {q : ℕ}
    (hq : q < n * n) :
    (pairFlags n X Y V).getD q 0 = 1 ↔ ∃ c ∈ lemmaFInstances (aeLevels U),
      (aeFlags n (instAB U V c.1 c.2) (instBC n U Y c.1) (instAC U X c.1)).getD q 0 = 1 := by
  have hn : 0 < n := by rcases n with _ | n <;> simp_all
  have hi : q / n < n := by rwa [Nat.div_lt_iff_lt_mul hn]
  have hj : q % n < n := Nat.mod_lt q hn
  have hqe : q / n * n + q % n = q := Nat.div_add_mod' q n
  have hbN := lt_two_pow_aeLevels U
  have hb : (3 * U : ℤ) < 2 ^ aeLevels U := by exact_mod_cast hbN
  -- the matrices as functions on `Fin n`
  set A : Fin n → Fin n → ℤ := fun i k => X.getD (i * n + k) 0 with hA
  set B : Fin n → Fin n → ℤ := fun k j => Y.getD (k * n + j) 0 with hB
  set t : Fin n → Fin n → ℤ := fun i j => V.getD (i * n + j) 0 with ht
  have hidx : ∀ a b : Fin n, a * n + b < n * n := fun a b => by nlinarith [a.2, b.2]
  have hmem : ∀ (l : List ℤ), l.length = n * n → ∀ a b : Fin n, l.getD (a * n + b) 0 ∈ l :=
    fun l hl a b => by
      rw [List.getD_eq_getElem _ _ (hl ▸ hidx a b)]
      exact List.getElem_mem _
  have key := exists_lt_iff_exists_exactTriangle A B t (W := U) (b := aeLevels U)
    (fun i k => hX _ (hmem X hlX i k)) (fun k j => hY _ (hmem Y hlY k j)) (by omega)
    (fun i j => by
      have := abs_le.1 (hV _ (hmem V hlV i j))
      exact ⟨by simp only [ht]; omega, by simp only [ht]; omega⟩) ⟨q / n, hi⟩ ⟨q % n, hj⟩
  simp only [hA, hB, ht, hqe] at key
  have hrange : ∀ f : ℕ → ℤ, ((List.range (n * n)).map f).getD q 0 = f q := fun f => by
    simp [List.getD_eq_getElem?_getD, List.getElem?_range hq]
  simp only [pairFlags, aeFlags, hrange, flag_eq_one_iff]
  rw [show (∃ k < n, X.getD (q / n * n + k) 0 + Y.getD (k * n + q % n) 0 < V.getD q 0) ↔
      ∃ k : Fin n, X.getD (q / n * n + k) 0 + Y.getD (k * n + q % n) 0 < V.getD q 0 from
    ⟨fun ⟨k, hk, h⟩ => ⟨⟨k, hk⟩, h⟩, fun ⟨k, h⟩ => ⟨k, k.2, h⟩⟩, key]
  refine exists_congr fun c => and_congr_right fun hc => ?_
  have hmap : ∀ (l : List ℤ) (f : ℤ → ℤ) (idx : ℕ), idx < n * n → l.length = n * n →
      (l.map f).getD idx 0 = f (l.getD idx 0) := fun l f idx h hl => getD_map_of_lt f (hl ▸ h)
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, k.2, ?_⟩
    simp only [instAB, instBC, instAC, affL, etIK, etKJ, etJI] at hk ⊢
    rw [hmap _ _ _ hq (by simp [hlV]), hmap _ _ _ hq (by simp [hlV]), hmap _ _ _ hq hlV,
      hmap _ _ _ (hidx ⟨q % n, hj⟩ k) (by simp), transposeL_getD _ _ hj k.2,
      hmap _ _ _ (hidx ⟨q / n, hi⟩ k) (by simp [hlX]), hmap _ _ _ (hidx ⟨q / n, hi⟩ k) hlX]
    simp only [prefQ, one_mul, hqe] at hk ⊢
    linarith
  · rintro ⟨k, hk, h⟩
    refine ⟨⟨k, hk⟩, ?_⟩
    simp only [instAB, instBC, instAC, affL, etIK, etKJ, etJI] at h ⊢
    rw [hmap _ _ _ hq (by simp [hlV]), hmap _ _ _ hq (by simp [hlV]), hmap _ _ _ hq hlV,
      hmap _ _ _ (hidx ⟨q % n, hj⟩ ⟨k, hk⟩) (by simp), transposeL_getD _ _ hj hk,
      hmap _ _ _ (hidx ⟨q / n, hi⟩ ⟨k, hk⟩) (by simp [hlX]),
      hmap _ _ _ (hidx ⟨q / n, hi⟩ ⟨k, hk⟩) hlX] at h
    simp only [prefQ, one_mul, hqe] at h ⊢
    linarith

end Lists

/-! ## The disjunction of the flags of the instances asked so far -/

/-- The flags of the pairs: cell `q` holds 1 if some instance `c` with `S c` has the flag 1 at
`q`, where `hit c q` says that it has. -/
noncomputable def orFlags (N : ℕ) (S : ℕ × ℤ → Prop) (hit : ℕ × ℤ → ℕ → Prop) : List ℤ :=
  (List.range N).map fun q => flag (∃ c, S c ∧ hit c q)

@[simp] theorem length_orFlags (N : ℕ) (S : ℕ × ℤ → Prop) (hit : ℕ × ℤ → ℕ → Prop) :
    (orFlags N S hit).length = N := by
  simp [orFlags]

theorem orFlags_mem (N : ℕ) (S : ℕ × ℤ → Prop) (hit : ℕ × ℤ → ℕ → Prop) :
    ∀ z ∈ orFlags N S hit, z = 0 ∨ z = 1 := by
  intro z hz
  obtain ⟨q, -, rfl⟩ := List.mem_map.1 hz
  unfold flag
  split_ifs <;> simp

/-- Before any question the flags are zero. -/
theorem orFlags_false (N : ℕ) (hit : ℕ × ℤ → ℕ → Prop) {l : List ℤ} (hl : l.length = N) :
    orFlags N (fun _ => False) hit = affL 0 0 l := by
  refine List.ext_getElem (by simp [hl]) fun i h1 h2 => ?_
  simp [orFlags, affL, flag]

/-- The disjunction with the flags of one more instance. -/
theorem orL_orFlags {N : ℕ} {S : ℕ × ℤ → Prop} {hit : ℕ × ℤ → ℕ → Prop} {c : ℕ × ℤ} {F : List ℤ}
    (hF : F.length = N) (hhit : ∀ q < N, hit c q ↔ F.getD q 0 = 1)
    (h01 : ∀ f ∈ F, f = 0 ∨ f = 1) :
    orL (orFlags N S hit) F = orFlags N (fun c' => S c' ∨ c' = c) hit := by
  refine List.ext_getElem (by simp [hF]) fun i h1 h2 => ?_
  have hi : i < N := by simpa using h2
  have hFi : F.getD i 0 = F[i] := List.getD_eq_getElem _ _ (hF ▸ hi)
  have hc := hhit i hi
  rw [hFi] at hc
  simp only [orL, orFlags, List.getElem_zipWith, List.getElem_map, List.getElem_range]
  rcases h01 _ (List.getElem_mem (hF ▸ hi)) with h | h
  · rw [h, flag_congr (show (∃ c', (S c' ∨ c' = c) ∧ hit c' i) ↔ ∃ c', S c' ∧ hit c' i from
      ⟨fun ⟨c', hc', hh⟩ => ⟨c', hc'.resolve_right fun he => by
        rw [he] at hh; exact absurd (hc.1 hh) (by rw [h]; decide), hh⟩,
        fun ⟨c', hc', hh⟩ => ⟨c', Or.inl hc', hh⟩⟩)]
    ring
  · rw [h, flag_of (p := ∃ c', (S c' ∨ c' = c) ∧ hit c' i) ⟨c, Or.inr rfl, hc.2 h⟩]
    unfold flag
    split_ifs <;> ring

/-- The instances at the levels above `ℓ` (and at most `b`) with `r ∈ {2, 3}`. -/
def Above (ℓ b : ℕ) (c : ℕ × ℤ) : Prop := ℓ < c.1 ∧ c.1 ≤ b ∧ (c.2 = 2 ∨ c.2 = 3)

/-- The two questions at the level `ℓ + 1` bring the asked set from above `ℓ + 1` to above `ℓ`. -/
theorem above_step {ℓ b : ℕ} (h : ℓ + 1 ≤ b) (c : ℕ × ℤ) :
    ((Above (ℓ + 1) b c ∨ c = (ℓ + 1, 2)) ∨ c = (ℓ + 1, 3)) ↔ Above ℓ b c := by
  obtain ⟨l, r⟩ := c
  simp only [Above, Prod.mk.injEq]
  constructor
  · rintro ((⟨h1, h2, h3⟩ | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) <;> omega
  · rintro ⟨h1, h2, h3⟩
    by_cases hl : l = ℓ + 1
    · subst hl
      rcases h3 with rfl | rfl <;> simp
    · exact Or.inl (Or.inl ⟨by omega, h2, h3⟩)

/-- Nothing has been asked at the top. -/
theorem above_self (b : ℕ) (c : ℕ × ℤ) : ¬ Above b b c := fun h => by
  have := h.1
  have := h.2.1
  omega

/-- After the questions at the level `0`, all instances of Lemma F have been asked. -/
theorem above_zero_iff (b : ℕ) (c : ℕ × ℤ) :
    (((Above 0 b c ∨ c = (0, 2)) ∨ c = (0, 3)) ∨ c = (0, 1)) ↔ c ∈ lemmaFInstances b := by
  obtain ⟨l, r⟩ := c
  simp only [Above, Prod.mk.injEq, lemmaFInstances, Finset.mem_insert, Finset.mem_product,
    Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (((⟨h1, h2, h3⟩ | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩)
    · exact Or.inr ⟨by omega, h3⟩
    · exact Or.inr ⟨by omega, Or.inl rfl⟩
    · exact Or.inr ⟨by omega, Or.inr rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
  · rintro (⟨rfl, rfl⟩ | ⟨h1, h3⟩)
    · exact Or.inr ⟨rfl, rfl⟩
    · by_cases hl : l = 0
      · subst hl
        rcases h3 with rfl | rfl <;> simp
      · exact Or.inl (Or.inl (Or.inl ⟨by omega, by omega, h3⟩))

/-- **The flags of all pairs** are the disjunction of the flags of the instances of Lemma F. -/
theorem orFlags_eq_pairFlags {n U : ℕ} {X Y V : List ℤ} (hX : AbsLe X U) (hY : AbsLe Y U)
    (hV : AbsLe V U) (hlX : X.length = n * n) (hlY : Y.length = n * n) (hlV : V.length = n * n) :
    orFlags (n * n) (fun c => c ∈ lemmaFInstances (aeLevels U))
      (fun c q => (aeFlags n (instAB U V c.1 c.2) (instBC n U Y c.1) (instAC U X c.1)).getD q 0 = 1)
      = pairFlags n X Y V := by
  refine List.ext_getElem (by simp [pairFlags]) fun q h1 h2 => ?_
  have hq : q < n * n := by simpa using h1
  have h := pairFlags_iff hX hY hV hlX hlY hlV hq
  rw [List.getD_eq_getElem _ _ (by simp [pairFlags, hq])] at h
  simp only [orFlags, List.getElem_map, List.getElem_range]
  by_cases hp : (pairFlags n X Y V)[q] = 1
  · rw [hp, flag_of (h.1 hp)]
  · rw [flag_of_not fun hh => hp (h.2 hh)]
    have : (pairFlags n X Y V)[q] = 0 ∨ (pairFlags n X Y V)[q] = 1 := by
      simp only [pairFlags, List.getElem_map, List.getElem_range]
      unfold flag
      split_ifs <;> simp
    omega

end ImprovedExponents.AllEdges
