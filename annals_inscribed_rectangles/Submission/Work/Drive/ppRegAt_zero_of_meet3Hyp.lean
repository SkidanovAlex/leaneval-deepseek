import Mathlib
import Submission.Work.Drive.encodedTransverse
import Submission.Work.Drive.meet32_bordism_invariance
import Submission.Work.Drive.ppParity.Defs
import Submission.Work.Drive.PPRegAt_chart_indep
import Submission.Work.Drive.surjective_endPairMap_of_tripleTransverse
import Submission.Work.Drive.ppRegCoord

namespace Work.Drive

open scoped Manifold ContDiff Topology
open Manifold Set Filter

/-!
# The base-collar regularity `PPRegAt` at `s = 0`, from the triple meet hypothesis

`Work.Drive.PPRegAt E E' V W x` asks for the surjectivity of the `x`-derivative of the *self-centred
charted* pair map `ppDiff` at a meet `x`, and for the surjectivity of its restriction to the coordinate
hyperplane at a boundary meet.  This file proves it at the base `s = 0` of a collapse family, where the
first chart block degenerates: by the hypotheses `hE0`/`hE'0` the meet at `s = 0` is a **triple** meet
of the three `3`-chains `D 0, D 1, D 2` at the triple point `Work.Drive.triPt x = (mk3 (ftU x) 1, ftY x,
ftZ x)` — block `0` sitting on the **top face** (level coordinate `1`) of its cube — while `V = D 1` and
`W = D 2`.  The proof is a chain of three steps.

1. **The triple point is transverse, with a usable common direction.**  `Meet3Hyp.trans` at `triPt x`
   gives the transversality of the three *manifold* derivatives `md3 D k (triPt x)`, and
   `Meet3Hyp.face` there gives a common direction.  Since at the triple point the three values coincide
   with the chart centre `E (ftS x) (ftU x)`, the three changes of coordinates `TParity.tc` are equal —
   in fact the identity (`tangentCoordChange_self`) — so both fields transport verbatim to the *charted*
   derivatives `G k = tc ∘ md3`.  The only boundary coordinate of `triPt x` is the level coordinate `2`
   of block `0` (the plane coordinates of block `0` and all of blocks `1`, `2` are strictly interior by
   `hu`, `hy`, `hz`), so the face clause's index is forced to be `(k, i) = (0, 2)`: the common direction
   has **non-zero third coordinate** `(v 0) 2 ≠ 0`, i.e. it points out of the level-`0` hyperplane
   `range ins2`.
2. **The pair map of the base is the flat pair map of the triple.**  Pulling `ppDiff` back along the
   coordinate projection `rho9` (the point of the `9`-box with the family coordinate replaced by `0`),
   the function `z ↦ ppDiff p p' E E' V W (rho9 z)` becomes

   > `z ↦ (χ (D 0 (mk3 (ftU z) 1)) − χ (D 1 (ftY z)), χ (D 0 (mk3 (ftU z) 1)) − χ (D 2 (ftZ z)))`,

   whose `x`-derivative is computed block by block (`HasFDerivAt` of `chr ∘ D k ∘` the block projection,
   via `fderiv_chart_comp_hasFDerivAt` and the Fréchet chain rule).  It is the linear map `L` of the
   statement of the proof, with first block `G 0 ∘ ins2 ∘ ftUCLM` and the two sweep blocks `G 1 ∘ ftYCLM`,
   `G 2 ∘ ftZCLM`.
3. **`L` is onto, and it is the derivative of `ppDiff` restricted to the `rho9`-hyperplane.**  Step 1
   feeds `Work.Drive.exists_flat_solution_of_tripleTransverse` (with `mk = ins2`, onto the level-`0`
   hyperplane): every target pair is realised by `(mkZ9 u y z)`, so `L` is surjective.  The chain rule
   for `fderiv` finally identifies `L` with `fderiv (ppDiff …) x ∘ rho9`, which transfers the
   surjectivity to `fderiv (ppDiff …) x` — and, since `rho9` fixes every point with `ftS = 0`, also to
   its restriction to the hyperplane `{v | v 0 = 0}`, which is the face clause at the only possible
   boundary coordinate `0`.
-/

theorem ppRegAt_zero_of_meet3Hyp {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {E : ℝ → EuclideanSpace ℝ (Fin 2) → M}
    {E' : ℝ → EuclideanSpace ℝ (Fin 2) → M}
    {V W : EuclideanSpace ℝ (Fin 3) → M}
    {D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M}
    (hD : Work.Drive.Meet3Hyp M D)
    (hsmooth : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 9)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin 9) => E (Work.Drive.ftS z) (Work.Drive.ftU z)))
    (hsmooth' : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 9)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin 9) => E' (Work.Drive.ftS z) (Work.Drive.ftU z)))
    (hsmoothV : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 9)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin 9) => V (Work.Drive.ftY z)))
    (hsmoothW : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 9)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin 9) => W (Work.Drive.ftZ z)))
    (hE0 : ∀ u : EuclideanSpace ℝ (Fin 2), E 0 u = D 0 (Work.Drive.mk3 u 1))
    (hE'0 : ∀ u : EuclideanSpace ℝ (Fin 2), E' 0 u = D 0 (Work.Drive.mk3 u 1))
    (hV : ∀ y : EuclideanSpace ℝ (Fin 3), V y = D 1 y)
    (hW : ∀ z : EuclideanSpace ℝ (Fin 3), W z = D 2 z)
    {x : EuclideanSpace ℝ (Fin 9)} (hx : x ∈ Work.Drive.ppMeet E E' V W)
    (hs : Work.Drive.ftS x = 0)
    (hu : ∀ i : Fin 2, Work.Drive.ftU x i ∈ Set.Ioo (0 : ℝ) 1)
    (hy : ∀ i : Fin 3, Work.Drive.ftY x i ∈ Set.Ioo (0 : ℝ) 1)
    (hz : ∀ i : Fin 3, Work.Drive.ftZ x i ∈ Set.Ioo (0 : ℝ) 1) :
    Work.Drive.PPRegAt E E' V W x := by
  -- ### the two chart centres coincide
  have hp'p : E' (Work.Drive.ftS x) (Work.Drive.ftU x)
      = E (Work.Drive.ftS x) (Work.Drive.ftU x) := by
    rw [hs, hE'0, hE0]
  -- ### the chart region of the self-centred chart pair
  have hres : x ∈ Work.Drive.ppRegion (E (Work.Drive.ftS x) (Work.Drive.ftU x))
      (E' (Work.Drive.ftS x) (Work.Drive.ftU x)) E E' V W := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact mem_chart_source _ _
    · rw [hx.2.1]; exact mem_chart_source _ _
    · exact mem_chart_source _ _
    · rw [hx.2.2]; exact mem_chart_source _ _
  -- ### the charted derivatives of the three chains at the base triple point
  set G0 : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
    (TParity.tc (E (ftS x) (ftU x)) D 0 (triPt x)).comp (TParity.md3 D 0 (triPt x)) with hG0
  set G1 : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
    (TParity.tc (E (ftS x) (ftU x)) D 1 (triPt x)).comp (TParity.md3 D 1 (triPt x)) with hG1
  set G2 : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
    (TParity.tc (E (ftS x) (ftU x)) D 2 (triPt x)).comp (TParity.md3 D 2 (triPt x)) with hG2
  -- ### the triple transversality and the common direction at the base
  have hvalD0 : D 0 (TParity.bPartC 0 (triPt x)) = E (ftS x) (ftU x) := by
    rw [bPartC_triPt_zero, ← hE0 (ftU x), hs]
  have hvalD1 : D 1 (TParity.bPartC 1 (triPt x)) = E (ftS x) (ftU x) := by
    rw [bPartC_triPt_one, ← hV (ftY x), hx.2.1]
  have hvalD2 : D 2 (TParity.bPartC 2 (triPt x)) = E (ftS x) (ftU x) := by
    rw [bPartC_triPt_two, ← hW (ftZ x), ← hx.2.2, hp'p]
  -- ### the triple point of `D` and its box data
  set v3 : Fin 3 → EuclideanSpace ℝ (Fin 3) :=
    ![Work.Drive.mk3 (ftU x) 1, ftY x, ftZ x] with hv3
  have hv3_0 : v3 0 = Work.Drive.mk3 (ftU x) 1 := by rw [hv3]; simp
  have hv3_1 : v3 1 = ftY x := by rw [hv3]; simp
  have hv3_2 : v3 2 = ftZ x := by rw [hv3]; simp
  have htri : triPt x = TParity.mk3 v3 := by rw [triPt, hv3]
  have hboxC : Work.Drive.mk3 (ftU x) 1 ∈ Submission.Drive.unitBox 2 := by
    intro i
    have h0 : (Work.Drive.mk3 (ftU x) 1 : EuclideanSpace ℝ (Fin 3)) 0 ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨le_of_lt (hu 0).1, le_of_lt (hu 0).2⟩
    have h1 : (Work.Drive.mk3 (ftU x) 1 : EuclideanSpace ℝ (Fin 3)) 1 ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨le_of_lt (hu 1).1, le_of_lt (hu 1).2⟩
    have h2 : (Work.Drive.mk3 (ftU x) 1 : EuclideanSpace ℝ (Fin 3)) 2 ∈ Set.Icc (0 : ℝ) 1 := by
      rw [Work.Drive.mk3_apply_two]
      norm_num
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  have hboxY : ftY x ∈ Submission.Drive.unitBox 2 := by
    intro i
    exact ⟨le_of_lt (hy i).1, le_of_lt (hy i).2⟩
  have hboxZ : ftZ x ∈ Submission.Drive.unitBox 2 := by
    intro i
    exact ⟨le_of_lt (hz i).1, le_of_lt (hz i).2⟩
  have hbox : ∀ k : Fin 3, v3 k ∈ Submission.Drive.unitBox 2 := by
    intro k
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with h | h | h
    · rw [h, hv3_0]; exact hboxC
    · rw [h, hv3_1]; exact hboxY
    · rw [h, hv3_2]; exact hboxZ
  have hv0E : D 0 (v3 0) = E (ftS x) (ftU x) := by
    rw [hv3_0, ← hE0 (ftU x), hs]
  have hv0E' : D 0 (v3 0) = E' (ftS x) (ftU x) := by
    rw [hv3_0, ← hE'0 (ftU x), hs]
  have h01 : D 0 (v3 0) = D 1 (v3 1) := by
    rw [hv0E, hv3_1, hx.2.1, hV]
  have h02 : D 0 (v3 0) = D 2 (v3 2) := by
    rw [hv0E', hv3_2, hx.2.2, hW]
  have hbdry : ∃ k : Fin 3, v3 k ∈ Submission.Drive.unitBoxBdry 2 := by
    refine ⟨0, ?_⟩
    rw [hv3_0]
    exact ⟨hboxC, ⟨(2 : Fin 3), Or.inr (Work.Drive.mk3_apply_two (ftU x) 1)⟩⟩
  -- ### the change of coordinates at the base triple point is the identity
  have htc0 : TParity.tc (E (ftS x) (ftU x)) D 0 (triPt x)
      = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 4)) := by
    ext v
    rw [TParity.tc, hvalD0, tangentCoordChange_self (mem_extChartAt_source _)]
    rfl
  have htc1 : TParity.tc (E (ftS x) (ftU x)) D 1 (triPt x)
      = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 4)) := by
    ext v
    rw [TParity.tc, hvalD1, tangentCoordChange_self (mem_extChartAt_source _)]
    rfl
  have htc2 : TParity.tc (E (ftS x) (ftU x)) D 2 (triPt x)
      = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 4)) := by
    ext v
    rw [TParity.tc, hvalD2, tangentCoordChange_self (mem_extChartAt_source _)]
    rfl
  have hmd0 : TParity.md3 D 0 (triPt x) = mfderiv (𝓡 3) (𝓡 4) (D 0) (v3 0) := by
    rw [TParity.md3, htri, TParity.bPartC_mk3]
  have hmd1 : TParity.md3 D 1 (triPt x) = mfderiv (𝓡 3) (𝓡 4) (D 1) (v3 1) := by
    rw [TParity.md3, htri, TParity.bPartC_mk3]
  have hmd2 : TParity.md3 D 2 (triPt x) = mfderiv (𝓡 3) (𝓡 4) (D 2) (v3 2) := by
    rw [TParity.md3, htri, TParity.bPartC_mk3]
  have hG0' : G0 = mfderiv (𝓡 3) (𝓡 4) (D 0) (v3 0) := by
    rw [hG0, htc0, ContinuousLinearMap.id_comp, hmd0]
  have hG1' : G1 = mfderiv (𝓡 3) (𝓡 4) (D 1) (v3 1) := by
    rw [hG1, htc1, ContinuousLinearMap.id_comp, hmd1]
  have hG2' : G2 = mfderiv (𝓡 3) (𝓡 4) (D 2) (v3 2) := by
    rw [hG2, htc2, ContinuousLinearMap.id_comp, hmd2]
  have hbase : TripleTransverse G0 G1 G2 ∧
      ∃ v : Fin 3 → EuclideanSpace ℝ (Fin 3),
        TripleCommonDir G0 G1 G2 v ∧ (v 0) 2 ≠ 0 := by
    refine ⟨?_, ?_⟩
    · rw [hG0', hG1', hG2']
      exact hD.trans v3 hbox h01 h02
    · obtain ⟨k, i, -, hsk, hso, v, hvcd, hvne⟩ :=
        hD.face v3 hbox h01 h02 hbdry
      have hk0 : k = 0 := by
        by_contra hk
        have h := (hso 0 (Ne.symm hk) 2).2
        rw [hv3_0, Work.Drive.mk3_apply_two] at h
        exact absurd h (lt_irrefl 1)
      have hi2 : i = 2 := by
        by_contra hi
        have h := (hsk 2 (Ne.symm hi)).2
        rw [hk0, hv3_0, Work.Drive.mk3_apply_two] at h
        exact absurd h (lt_irrefl 1)
      refine ⟨v, ?_, ?_⟩
      · rw [hG0', hG1', hG2']
        exact hvcd
      · rw [hk0, hi2] at hvne
        exact hvne
  -- ### the three charted chain derivatives at the base
  have hmem0 : D 0 (TParity.bPartC 0 (triPt x)) ∈ (chr (E (ftS x) (ftU x))).source := by
    rw [hvalD0]; exact mem_chart_source _ _
  have hmem1 : D 1 (TParity.bPartC 1 (triPt x)) ∈ (chr (E (ftS x) (ftU x))).source := by
    rw [hvalD1]; exact mem_chart_source _ _
  have hmem2 : D 2 (TParity.bPartC 2 (triPt x)) ∈ (chr (E (ftS x) (ftU x))).source := by
    rw [hvalD2]; exact mem_chart_source _ _
  have hchart0 : HasFDerivAt (fun a : EuclideanSpace ℝ (Fin 3) =>
      chr (E (ftS x) (ftU x)) (D 0 a)) G0 (Work.Drive.mk3 (ftU x) 1) := by
    rw [hG0, ← bPartC_triPt_zero x]
    exact fderiv_chart_comp_hasFDerivAt (D 0) (hD.smooth 0) (E (ftS x) (ftU x)) hmem0
  have hchart1 : HasFDerivAt (fun a : EuclideanSpace ℝ (Fin 3) =>
      chr (E (ftS x) (ftU x)) (D 1 a)) G1 (ftY x) := by
    rw [hG1, ← bPartC_triPt_one x]
    exact fderiv_chart_comp_hasFDerivAt (D 1) (hD.smooth 1) (E (ftS x) (ftU x)) hmem1
  have hchart2 : HasFDerivAt (fun a : EuclideanSpace ℝ (Fin 3) =>
      chr (E (ftS x) (ftU x)) (D 2 a)) G2 (ftZ x) := by
    rw [hG2, ← bPartC_triPt_two x]
    exact fderiv_chart_comp_hasFDerivAt (D 2) (hD.smooth 2) (E (ftS x) (ftU x)) hmem2
  -- ### the charted derivatives of the three blocks of the pair map
  have hftU : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 9) => ftU z) ftUCLM x :=
    ftUCLM.hasFDerivAt.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun z => (ftUCLM_eq z).symm)
  have hftY : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 9) => ftY z) ftYCLM x :=
    ftYCLM.hasFDerivAt.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun z => (ftYCLM_eq z).symm)
  have hftZ : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 9) => ftZ z) ftZCLM x :=
    ftZCLM.hasFDerivAt.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun z => (ftZCLM_eq z).symm)
  have hA : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 9) =>
      chr (E (ftS x) (ftU x)) (D 0 (Work.Drive.mk3 (ftU z) 1)))
      (G0.comp (ins2.comp ftUCLM)) x := by
    have h1 : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 9) => ins2 (ftU z))
        (ins2.comp ftUCLM) x := ins2.hasFDerivAt.comp x hftU
    have h2 := h1.add_const (Work.Drive.mk3 (0 : EuclideanSpace ℝ (Fin 2)) 1)
    have h3 : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 9) =>
        Work.Drive.mk3 (ftU z) 1) (ins2.comp ftUCLM) x :=
      h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => (mk3_one_eq (ftU z)))
    have h4 := hchart0.comp x h3
    simpa only [Function.comp_def] using h4
  have hB : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 9) =>
      chr (E (ftS x) (ftU x)) (D 1 (ftY z))) (G1.comp ftYCLM) x := by
    have h4 := hchart1.comp x hftY
    simpa only [Function.comp_def] using h4
  have hC : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 9) =>
      chr (E (ftS x) (ftU x)) (D 2 (ftZ z))) (G2.comp ftZCLM) x := by
    have h4 := hchart2.comp x hftZ
    simpa only [Function.comp_def] using h4
  -- ### the derivative of the pull-back of `ppDiff` along `rho9`
  set L : EuclideanSpace ℝ (Fin 9) →L[ℝ] EuclideanSpace ℝ (Fin 8) :=
    TParity.pUpCLM.comp
      (((G0.comp (ins2.comp ftUCLM)) - (G1.comp ftYCLM)).prod
        ((G0.comp (ins2.comp ftUCLM)) - (G2.comp ftZCLM))) with hL
  have hfun : (fun z : EuclideanSpace ℝ (Fin 9) =>
      TParity.pUp (chr (E (ftS x) (ftU x)) (D 0 (Work.Drive.mk3 (ftU z) 1))
             - chr (E (ftS x) (ftU x)) (D 1 (ftY z)))
          (chr (E (ftS x) (ftU x)) (D 0 (Work.Drive.mk3 (ftU z) 1))
             - chr (E (ftS x) (ftU x)) (D 2 (ftZ z))))
      = fun z => ppDiff (E (ftS x) (ftU x)) (E' (ftS x) (ftU x)) E E' V W (rho9 z) := by
    funext z
    simp only [ppDiff, pair44_eq_pairUp, ftS_rho9, ftU_rho9, ftY_rho9, ftZ_rho9,
      hE0 (ftU z), hE'0 (ftU z), hV (ftY z), hW (ftZ z), hp'p]
  have hderiv : HasFDerivAt
      (fun z => ppDiff (E (ftS x) (ftU x)) (E' (ftS x) (ftU x)) E E' V W (rho9 z)) L x := by
    rw [hL]
    exact hfun ▸ (TParity.hasFDerivAt_pUp (hA.sub hB) (hA.sub hC))
  -- ### the linear map `L` is onto
  have hLsurj : Function.Surjective L := by
    intro w
    rw [hL]
    obtain ⟨u, y, z, h1, h2⟩ := exists_flat_solution_of_tripleTransverse ins2
      (fun v hv => exists_ins2_eq_of_two_eq_zero hv) G0 G1 G2 hbase.1 hbase.2
      (TParity.fst8 w) (TParity.snd8 w)
    refine ⟨mkZ9 u y z, ?_⟩
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      sub_apply, ftUCLM_mkZ9, ftYCLM_mkZ9, ftZCLM_mkZ9, h1, h2,
      TParity.pUpCLM_apply, TParity.pUp_fst8_snd8]
  -- ### the derivative of `ppDiff` itself, on the hyperplane `{0}`-coordinates
  have hQdiff : DifferentiableAt ℝ
      (ppDiff (E (ftS x) (ftU x)) (E' (ftS x) (ftU x)) E E' V W) x :=
    (PPIndep.hasFDerivAt_ppDiff E E' V W hsmooth hsmooth' hsmoothV hsmoothW hx hres).differentiableAt
  have hρ9x : rho9 x = x := rho9_fixed x (show x 0 = 0 from hs)
  have hQdiff' : DifferentiableAt ℝ
      (ppDiff (E (ftS x) (ftU x)) (E' (ftS x) (ftU x)) E E' V W) (rho9 x) := by
    rw [hρ9x]; exact hQdiff
  have hkey : L = (fderiv ℝ
      (ppDiff (E (ftS x) (ftU x)) (E' (ftS x) (ftU x)) E E' V W) x).comp rho9 := by
    have h2 : HasFDerivAt
        ((ppDiff (E (ftS x) (ftU x)) (E' (ftS x) (ftU x)) E E' V W) ∘ rho9) L x := hderiv
    have h1 : HasFDerivAt
        ((ppDiff (E (ftS x) (ftU x)) (E' (ftS x) (ftU x)) E E' V W) ∘ rho9)
        ((fderiv ℝ (ppDiff (E (ftS x) (ftU x)) (E' (ftS x) (ftU x)) E E' V W) x).comp rho9) x := by
      have hc := hQdiff'.hasFDerivAt.comp x rho9.hasFDerivAt
      rwa [hρ9x] at hc
    exact h2.unique h1
  -- ### the two conclusions
  refine ⟨?_, ?_⟩
  · intro w
    obtain ⟨q, hq⟩ := hLsurj w
    refine ⟨rho9 q, ?_⟩
    rw [hkey, ContinuousLinearMap.comp_apply] at hq
    exact hq
  · intro _
    refine ⟨0, ?_, ?_, ?_⟩
    · exact Or.inl hs
    · intro j hj
      fin_cases j
      · exact absurd rfl hj
      · simpa [ftU, WithLp.ofLp_toLp] using hu 0
      · simpa [ftU, WithLp.ofLp_toLp] using hu 1
      · simpa [ftY, WithLp.ofLp_toLp] using hy 0
      · simpa [ftY, WithLp.ofLp_toLp] using hy 1
      · simpa [ftY, WithLp.ofLp_toLp] using hy 2
      · simpa [ftZ, WithLp.ofLp_toLp] using hz 0
      · simpa [ftZ, WithLp.ofLp_toLp] using hz 1
      · simpa [ftZ, WithLp.ofLp_toLp] using hz 2
    · intro w
      obtain ⟨q, hq⟩ := hLsurj w
      refine ⟨⟨rho9 q, rho9_zero q⟩, ?_⟩
      rw [hkey, ContinuousLinearMap.comp_apply] at hq
      exact hq

end Work.Drive
