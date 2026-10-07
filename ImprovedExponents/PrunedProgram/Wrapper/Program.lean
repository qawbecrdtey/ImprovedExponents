module

public import ImprovedExponents.PrunedProgram.Shared.Stage
public import ImprovedExponents.PrunedProgram.Pre.Preprocessing
public import ImprovedExponents.PrunedProgram.Query.Query
public import ImprovedExponents.PrunedProgram.Wrapper.Task
public import ImprovedExponents.Pipeline.RegimeRS

@[expose] public section

/-!
# The pruned thin-product solver as a program, and as an offline routine

`programP G r s` is `programRS G r s` (upstream's `program31 G` with the regime test `D^r ≤ N^s`)
followed by the seven procedures of the pruned solver: the encoder with a budget of symbols `P₀`,
the encodings of all bands, the shared stage, the preprocessing of Theorem 30, the preprocessing
and the offline routine with rational parameters, and the solver of all instances
(`ImprovedExponents.PrunedProgram.Procs`).  Every other procedure — the band arrays, the slices,
the tiles, the queries, the padding — is upstream's and keeps its number.

The entries are assembled as upstream's are (`ThreeSumApsp/Programs/Sec4/ChoosingParameters/
Program.lean`, `Theorem30/Program.lean`): the shared stage from `sharedP_entry`, the
preprocessing from `preCoreP_of_base58`, the queries from `queryAtP_of_base58`, and the routine
`offline32P` from `pre31P_meets`, `query31P_meets` and `offline32P_meets`, all with the constant
`cShared30` of upstream's shared stage.  `offline32PRoutine G r s` packages the routine for the
generic solver of `ImprovedExponents.Pipeline.ThinClaim`.

Adapted from upstream (Apache-2.0).
-/

namespace ImprovedExponents

open ThreeSumApsp ThreeSumApsp.Spec Light Light.Sec3 Light.Sec4

/-- The bodies of the procedures number 77 to 83. -/
def procsP (G : RatParams) : List Stmt :=
  [Sec2.encodePBody Sec2.pEncStep Proc.encodeP, Sec2.encodeBandsPBody, Sec2.sharedPBody,
    preCorePBody, pre31PBody G, offline32PBody, allBody Proc.testRS Proc.offline32P]

/-- The pruned solver: `programRS G r s` followed by the seven new procedures. -/
def programP (G : RatParams) (r s : ℕ) : Program := programRS G r s ++ procsP G

/-- `programRS G r s` has 77 procedures. -/
theorem length_programRS (G : RatParams) (r s : ℕ) : (programRS G r s).length = 77 := rfl

/-- The new procedures stand at their numbers. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Program.lean (program31_at)
theorem programP_at (G : RatParams) (r s n : ℕ) {body : Stmt} (hn : 77 ≤ n := by norm_num)
    (h : (procsP G)[n - 77]? = some body := by rfl) : (programP G r s)[n]? = some body := by
  rw [programP, List.getElem?_append_right (by rw [length_programRS]; exact hn),
    length_programRS]
  exact h

/-- A procedure of `program31 G` is one of `programP G r s`, with the same number. -/
theorem programP_at_low (G : RatParams) (r s : ℕ) {n : ℕ} {body : Stmt}
    (h : (program31 G)[n]? = some body) : (programP G r s)[n]? = some body := by
  rw [programP, programRS, List.append_assoc]
  exact getElem?_append_of_eq_some h _

/-- The pruned solver begins with `base58`. -/
theorem programP_eq_base58 (G : RatParams) (r s : ℕ) :
    programP G r s = base58 ++
      (procs31 G ++ [powLtBody, testRSBody r s, allRSBody] ++ procsP G) := by
  simp only [programP, programRS, program31, List.append_assoc]

/-- The pruned solver begins with Section 2's `program5`. -/
theorem programP_eq_program5 (G : RatParams) (r s : ℕ) :
    programP G r s = Sec2.program5 ++
      ([Sec2.regimeBody, Sec2.thinBruteBody, Sec2.thinBody] ++ List.replicate 11 .skip ++ procs40
        ++ [preCoreBody, queryAtBody, wantedCoreBody, wantedMainBody] ++ procs31 G
        ++ [powLtBody, testRSBody r s, allRSBody] ++ procsP G) := by
  simp only [programP, programRS, program31, base58, Sec2.programThin, List.append_assoc]

/-! ## The entries -/

/-- **The pruned shared stage**, in `programP G r s`, with upstream's constant. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Program.lean (shared_base58)
theorem sharedP_programP (G : RatParams) (r s : ℕ) (lim : Limits) (std : Std lim) :
    Sec2.SharedSpecP lim (programP G r s) cShared30 := by
  have e := programP_eq_program5 G r s
  refine Sec2.sharedP_entry std (programP_at G r s Proc.sharedP)
    (programP_at G r s Proc.encodeBandsP) ?_ ?_ (programP_at G r s Proc.encodeP)
    (c := Sec2.cShared5) ?_ (by norm_num [Sec2.cShared5, Sec2.cBandArray, Sec2.cEncP]) le_rfl
  · rw [e]; exact Sec2.at_prefix rfl _
  · rw [e]; exact Sec2.at_prefix rfl _
  · rw [e]; exact Sec2.sharedCallees_of_prefix _ lim std

/-- **The pruned preprocessing of Theorem 30**, in `programP G r s`, for all limits. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Program.lean (preCore_base58)
theorem preCoreP_programP (G : RatParams) (r s : ℕ) :
    ∀ lim, PreCoreSpecP lim (programP G r s) cShared30 := by
  intro lim p t hmL aX aY b0 X Y U μ ht hlim
  exact preCoreP_of_base58 (programP_eq_base58 G r s) (programP_at G r s Proc.preCoreP)
    (sharedP_programP G r s lim hlim.std) p t hmL aX aY b0 X Y U μ ht hlim

/-- **A query at a given place of the memory**, in `programP G r s`, for all limits. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Program.lean (queryAt_base58)
theorem queryAtP_programP (G : RatParams) (r s : ℕ) : ∀ lim, QueryAtSpecP lim (programP G r s) :=
  fun _ => queryAtP_of_base58 (programP_eq_base58 G r s)

/-- **The pruned preprocessing with rational parameters**, in `programP G r s`, for all limits. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Program.lean
-- (pre31_program31)
theorem pre31P_programP (G : RatParams) (r s : ℕ) :
    ∀ lim, PreSpec31P lim (programP G r s) cShared30 G := by
  intro lim N D₀ aX aY fr X Y U μ hin
  have std := hin.lim.std
  have hcopy : CopySpec lim (programP G r s) :=
    copy_ok (programP_at_low G r s (program31_at G Proc.copy)) std
  have hfill : FillSpec lim (programP G r s) :=
    fill_ok (programP_at_low G r s (program31_at G Proc.fill)) std
  have hlog : Log4Spec lim (programP G r s) :=
    log4_meets (programP_at_low G r s (program31_at G Proc.log4)) std
  have hlev : CeilMulSpec lim (programP G r s) Proc.levels31 G.a G.b :=
    ceilMul_meets G.hb (programP_at_low G r s (program31_at G Proc.levels31))
  have hswi : CeilMulSpec lim (programP G r s) Proc.switch31 G.p G.q :=
    ceilMul_meets G.hq (programP_at_low G r s (program31_at G Proc.switch31))
  have hpad : PadXSpec lim (programP G r s) :=
    padX_meets (programP_at_low G r s (program31_at G Proc.padX)) hcopy hfill std
  exact pre31P_meets G (programP_at G r s Proc.pre31P)
    ⟨hlog, hlev, hswi, hpad, hcopy, hfill, preCoreP_programP G r s lim⟩ N D₀ aX aY fr X Y U μ hin

/-- **A query with rational parameters**, in `programP G r s`, for all limits. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Program.lean
-- (query31_program31)
theorem query31P_programP (G : RatParams) (r s : ℕ) :
    ∀ lim, QuerySpec31P lim (programP G r s) G := by
  intro lim N D₀ aX aY fr X Y U μ I J hin
  have hip : IpAtSpec lim (programP G r s) :=
    ipAt_meets (programP_at_low G r s (program31_at G Proc.ipAt)) hin.lim.std
  exact query31P_meets G (programP_at_low G r s (program31_at G Proc.query31))
    (queryAtP_programP G r s lim) hip N D₀ aX aY fr X Y U μ I J hin

/-- **The pruned offline routine**, in `programP G r s`, for all limits. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Program.lean
-- (offline32_program31)
theorem offline32P_programP (G : RatParams) (r s : ℕ) :
    ∀ lim, OfflineSpec32P lim (programP G r s) cShared30 G :=
  fun lim => offline32P_meets (programP_at G r s Proc.offline32P) (pre31P_programP G r s lim)
    (query31P_programP G r s lim)

/-- A program that begins with `programP G r s` holds offline32P with its specification at the
parameters `G`, for all limits. -/
-- adapted from ImprovedExponents/Pipeline/ThinClaim.lean (offlineSpec32_of_program31)
theorem offlineSpec32P_of_programP {P : Program} {G : RatParams} {r s : ℕ}
    (h : ∃ Q, P = programP G r s ++ Q) (lim : Limits) : OfflineSpec32P lim P cShared30 G := by
  obtain ⟨Q, rfl⟩ := h
  exact (offline32P_programP G r s lim).append Q

/-! ## The routine -/

/-- **The pruned offline routine** at the parameters `G`, as an `OfflineRoutine`: it is specified
on the instances where the hypotheses of Theorem 30 hold from the threshold on, in the programs
that begin with `programP G r s`.  Its time is `tOffline32P cShared30 G`; its needs are those of
upstream's routine, since the pruned shared stage has the same layout and forms the same
numbers. -/
-- adapted from ImprovedExponents/Pipeline/ThinClaim.lean (offline32Routine)
def offline32PRoutine (G : RatParams) (r s : ℕ) : OfflineRoutine where
  Ok N D := G.m₀ ≤ logFour D → Hyp30 (parOf G N D) (switchOf31 G D)
  proc := Proc.offline32P
  body := offline32PBody
  aux P := ∃ Q, P = programP G r s ++ Q
  aux_append _ Q := fun ⟨R, h⟩ => ⟨R ++ Q, by rw [h, List.append_assoc]⟩
  time := tOffline32P cShared30 G
  time_mono N D _ _ hw := tOffline32P_mono cShared30 G N D hw
  need := offline32Need G
  need_poly := offline32Need_poly G
  meets haux _ hpre hfit ok :=
    offline32P_meets_thinTask (offlineSpec32P_of_programP haux _) hpre hfit ok

/-- `programP G r s` holds offline32P, the procedures it calls, and the solver of all instances
that calls it after the test `D^r ≤ N^s`. -/
theorem offline32PRoutine_programP (G : RatParams) (r s : ℕ) :
    (programP G r s)[Proc.offline32P]? = some offline32PBody ∧
      (offline32PRoutine G r s).aux (programP G r s) ∧
      (programP G r s)[Proc.allP]? = some (allBody Proc.testRS Proc.offline32P) :=
  ⟨programP_at G r s Proc.offline32P, ⟨[], (List.append_nil _).symm⟩,
    programP_at G r s Proc.allP⟩

end ImprovedExponents
