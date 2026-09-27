import Mathlib
import Submission.Work.Drive.ppParity.Defs
import Submission.Work.Drive.ppPairLinAlgOne
import Submission.Work.Drive.planeClassDeriv_eq_mfderiv
import Submission.Work.Drive.ChartBridge
import Submission.Work.Drive.ppRegAt_zero_of_meet3Hyp

/-- Shortcut instance (Lean v4.34 port): on v4.34 Mathlib the generic search for
`ContinuousSMul ℝ E` on real normed spaces such as `EuclideanSpace ℝ (Fin n)` or products of them
detours through `PolynormableSpace.continuousSMul` and exhausts the synthesis budget. -/
private local instance (priority := high) normedSpace_continuousSMul_real_v434 {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] : ContinuousSMul ℝ E :=
  IsBoundedSMul.continuousSMul


/-!
# The `s = 1` half of the collar regularity `PPRegAt`, from the pair data

`Work.Drive.ppRegAt_zero_of_meet3Hyp` proves `PPRegAt` at the base `ftS = 0` of the radial collapse,
where the two plane blocks of the pair map degenerate to the same chain and the datum is a *triple*
transversality.  This file proves the **other** half, at `ftS = 1`, where the two plane blocks are the
distinct chains `E 1` and `E' 1` and no triple is available; the hypothesis is the pair datum

* `hset` — the joint transversality of the two plane blocks against the two sweeps:
  `{a | A a ∈ range C ∧ B a ∈ range D} = 0`, i.e. `range A ⊓ range C = 0` and `B a ∉ range D` at the
  non-zero elements of `ker A`;
* `hC`, `hD` — the two sweeps are immersions at the meet.

These are exactly the hypotheses of `Work.Drive.surjective_pairDiffTwoCLM`
(`Submission/Work/Drive/ppPairLinAlgOne.lean`), so the `s = 1` obligation is, as recorded in
`Submission/Work/Drive/PPREGAT_S0_STATUS.md` §5, *literally* that surjectivity statement, transported
to the charted pair map.

## The proof

`PPRegAt E E' V W x` is a condition on the `x`-derivative of the **self-centred charted** pair map
`ppDiff p p' E E' V W` (`p = E (ftS x) (ftU x)`, `p' = E' (ftS x) (ftU x)`).  The two steps are the
same as at `s = 0`, with the *family* projection replaced by the projection onto the level `1`
hyperplane (the map `ppOnePi1`, which replaces the first coordinate of the `9`-box by `1`; it is a
translation of `rho9`, so its derivative is `rho9` and it fixes every point with `ftS = 1`):

1. **The flat map is onto.**  Pulling `ppDiff` back along `ppOnePi1` makes the first coordinate of the
   `9`-box constant `= 1`, so the pulled-back map is
   `z ↦ (χ (E 1 (ftU z)) − χ (V (ftY z)), χ' (E' 1 (ftU z)) − χ' (W (ftZ z)))` — a function of
   `(ftU z, ftY z, ftZ z)` alone.  Its derivative at `x` is
   `pUpCLM ∘ (pairDiffTwoCLM A B C D) ∘ ppOneBlockProj`
   with `A = ∂_u (E 1)`, `B = ∂_u (E' 1)`, `C = ∂V`, `D = ∂W` (the change-of-coordinates factors are
   the identity at a self-centred chart, `tangentCoordChange_self`), and it is onto by
   `surjective_pairDiffTwoCLM` (from `hset`, `hC`, `hD`), `ppOneBlockProj` being onto (`mkZ9`).
2. **Transport.**  The chart-free description of `fderiv (ppDiff)` at a meet
   (`Work.Drive.PPIndep.hasFDerivAt_ppDiff`) and the chain rule along `ppOnePi1` give
   `pUpCLM ∘ Λ = fderiv ppDiff x ∘ rho9`; since `rho9` restricted to the hyperplane `{v | v 0 = 0}` is
   the identity, the surjectivity of the flat map yields both clauses of `PPRegAt` at the boundary
   coordinate `0` (the only boundary coordinate, `x 0 = ftS x = 1` by `hs`).
-/

namespace Work.Drive

open scoped Manifold ContDiff Topology
open Manifold Set

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

noncomputable section

/-! ## The projection onto the level `1` hyperplane -/

/-- The vector of the `9`-box with first coordinate `1` and all other coordinates `0`. -/
def ppOneE9 : EuclideanSpace ℝ (Fin 9) := WithLp.toLp 2 (fun i : Fin 9 => if i = 0 then (1 : ℝ) else 0)

/-- **The projection onto the level-`1` hyperplane of the `9`-box**: the point with the first
coordinate replaced by `1` and the other coordinates unchanged.  It is `rho9 · + ppOneE9`, so its
derivative is `rho9`, and it fixes every point whose first coordinate is already `1`. -/
def ppOnePi1 (z : EuclideanSpace ℝ (Fin 9)) : EuclideanSpace ℝ (Fin 9) :=
  WithLp.toLp 2 (fun i : Fin 9 => if i = 0 then (1 : ℝ) else z i)

@[simp] lemma ppOne_ftS_pi1 (z : EuclideanSpace ℝ (Fin 9)) : ftS (ppOnePi1 z) = 1 := by simp [ppOnePi1, ftS]

@[simp] lemma ppOne_ftU_pi1 (z : EuclideanSpace ℝ (Fin 9)) : ftU (ppOnePi1 z) = ftU z := by
  ext i; fin_cases i <;> simp [ppOnePi1, ftU]

@[simp] lemma ppOne_ftY_pi1 (z : EuclideanSpace ℝ (Fin 9)) : ftY (ppOnePi1 z) = ftY z := by
  ext i; fin_cases i <;> simp [ppOnePi1, ftY]

@[simp] lemma ppOne_ftZ_pi1 (z : EuclideanSpace ℝ (Fin 9)) : ftZ (ppOnePi1 z) = ftZ z := by
  ext i; fin_cases i <;> simp [ppOnePi1, ftZ]

/-- `ppOnePi1` fixes the points of its own hyperplane. -/
lemma ppOne_pi1_fixed (x : EuclideanSpace ℝ (Fin 9)) (hx : x 0 = 1) : ppOnePi1 x = x := by
  ext i
  rcases Fin.eq_zero_or_eq_succ i with h | ⟨j, rfl⟩
  · subst h; simp [ppOnePi1, hx]
  · simp [ppOnePi1]

/-- The derivative of `ppOnePi1` is `rho9`. -/
lemma ppOne_hasFDerivAt_pi1 (x : EuclideanSpace ℝ (Fin 9)) : HasFDerivAt ppOnePi1 rho9 x := by
  have h1 : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 9) => rho9 z + ppOneE9) rho9 x :=
    rho9.hasFDerivAt.add_const ppOneE9
  have hbridge : (fun z : EuclideanSpace ℝ (Fin 9) => rho9 z + ppOneE9) = ppOnePi1 := by
    funext z
    ext i
    rcases Fin.eq_zero_or_eq_succ i with h | ⟨j, rfl⟩
    · subst h; simp [ppOnePi1, ppOneE9, rho9_zero]
    · have hj : (j.succ : Fin 9) ≠ 0 := by simp
      simp [ppOnePi1, ppOneE9, rho9_apply_of_ne, hj]
  rwa [hbridge] at h1

/-! ## The `(u, y, z)`-projection of the `9`-box -/

/-- The projection of the `9`-box onto its three parameters `(u, y, z)`. -/
def ppOneBlockProj : EuclideanSpace ℝ (Fin 9) →L[ℝ]
    (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :=
  ftUCLM.prod (ftYCLM.prod ftZCLM)

/-- The parameter projection is onto: every triple is `(ftU, ftY, ftZ)` of `mkZ9 u y z`. -/
lemma ppOneBlockProj_surjective : Function.Surjective ppOneBlockProj := by
  rintro ⟨u, y, z⟩
  exact ⟨mkZ9 u y z, by simp [ppOneBlockProj]⟩

/-! ## The change of coordinates at a self-centred chart -/

/-- At a self-centred chart pair the change of coordinates is the identity. -/
lemma ppOnePpTc_self {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M] (p : M) :
    PPIndep.ppTc p p = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 4)) := by
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [PPIndep.ppTc, ContinuousLinearMap.id_apply]
  exact tangentCoordChange_self (I := 𝓡 4) (mem_extChartAt_source p) (v := v)

/-! ## The slice `u ↦ (1, u)` -/

/-- The inclusion of the plane slice `s = 1` into the family parameter space. -/
lemma ppOneSlice_smooth : ContMDiff (𝓡 2) (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
    ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : EuclideanSpace ℝ (Fin 2) => ((1 : ℝ), u)) := by
  refine (contMDiff_prod_module_iff (fun u : EuclideanSpace ℝ (Fin 2) => ((1 : ℝ), u))).mpr ⟨?_, ?_⟩
  · show ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun _ : EuclideanSpace ℝ (Fin 2) => (1 : ℝ))
    exact contMDiff_const
  · show ContMDiff (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : EuclideanSpace ℝ (Fin 2) => u)
    exact contMDiff_id

theorem ppRegAt_one_of_pairData {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M}
    {V W : EuclideanSpace ℝ (Fin 3) → M}
    (hsmoothE : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry E))
    (hsmoothE' : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry E'))
    (hsmoothV : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hsmoothW : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    {x : EuclideanSpace ℝ (Fin 9)} (hx : x ∈ Work.Drive.ppMeet E E' V W)
    (hs : Work.Drive.ftS x = 1)
    (hu : ∀ i : Fin 2, Work.Drive.ftU x i ∈ Set.Ioo (0 : ℝ) 1)
    (hy : ∀ i : Fin 3, Work.Drive.ftY x i ∈ Set.Ioo (0 : ℝ) 1)
    (hz : ∀ i : Fin 3, Work.Drive.ftZ x i ∈ Set.Ioo (0 : ℝ) 1)
    (hset : ∀ a : EuclideanSpace ℝ (Fin 2),
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
        (fun u : EuclideanSpace ℝ (Fin 2) => E 1 u) (Work.Drive.ftU x)) a ∈
          (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) V (Work.Drive.ftY x)).range →
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
        (fun u : EuclideanSpace ℝ (Fin 2) => E' 1 u) (Work.Drive.ftU x)) a ∈
          (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) W (Work.Drive.ftZ x)).range →
      a = 0)
    (hC : Function.Injective (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) V (Work.Drive.ftY x)))
    (hD : Function.Injective (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) W (Work.Drive.ftZ x))) :
    Work.Drive.PPRegAt E E' V W x := by
  have hx0 : x 0 = 1 := hs
  -- ### the chart centres
  set p : M := E (ftS x) (ftU x) with hp
  set p' : M := E' (ftS x) (ftU x) with hp'
  have hEp : p = E 1 (ftU x) := by rw [hp, hs]
  have hE'p : p' = E' 1 (ftU x) := by rw [hp', hs]
  have hVp : V (ftY x) = p := by rw [← hx.2.1, ← hp]
  have hWp : W (ftZ x) = p' := by rw [← hx.2.2, ← hp']
  -- ### the chart region
  have hres : x ∈ ppRegion p p' E E' V W := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hp]; exact mem_chart_source _ _
    · rw [← hx.2.1, ← hp]; exact mem_chart_source _ _
    · rw [← hp']; exact mem_chart_source _ _
    · rw [← hx.2.2, ← hp']; exact mem_chart_source _ _
  -- ### smoothness of the four `9`-chains
  have hftS9 : ContMDiff (𝓡 9) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) (ftS) := by
    rw [contMDiff_iff_contDiff]
    show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : EuclideanSpace ℝ (Fin 9) => x 0)
    fun_prop
  have hftU9 : ContMDiff (𝓡 9) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ((⊤ : ℕ∞) : WithTop ℕ∞) ftU := by
    rw [contMDiff_iff_contDiff]
    show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin 9) => WithLp.toLp 2 (fun i : Fin 2 => x ⟨1 + i.val, by omega⟩))
    fun_prop
  have hftY9 : ContMDiff (𝓡 9) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ((⊤ : ℕ∞) : WithTop ℕ∞) ftY := by
    rw [contMDiff_iff_contDiff]
    show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin 9) => WithLp.toLp 2 (fun i : Fin 3 => x ⟨3 + i.val, by omega⟩))
    fun_prop
  have hftZ9 : ContMDiff (𝓡 9) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ((⊤ : ℕ∞) : WithTop ℕ∞) ftZ := by
    rw [contMDiff_iff_contDiff]
    show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin 9) => WithLp.toLp 2 (fun i : Fin 3 => x ⟨6 + i.val, by omega⟩))
    fun_prop
  have hE9 : ContMDiff (𝓡 9) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin 9) => E (ftS z) (ftU z)) :=
    hsmoothE.comp ((contMDiff_prod_module_iff (fun z : EuclideanSpace ℝ (Fin 9) => (ftS z, ftU z))).mpr
      ⟨hftS9, hftU9⟩)
  have hE'9 : ContMDiff (𝓡 9) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin 9) => E' (ftS z) (ftU z)) :=
    hsmoothE'.comp ((contMDiff_prod_module_iff (fun z : EuclideanSpace ℝ (Fin 9) => (ftS z, ftU z))).mpr
      ⟨hftS9, hftU9⟩)
  have hV9 : ContMDiff (𝓡 9) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin 9) => V (ftY z)) := hsmoothV.comp hftY9
  have hW9 : ContMDiff (𝓡 9) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin 9) => W (ftZ z)) := hsmoothW.comp hftZ9
  -- ### the two plane slices
  have hE1smooth : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : EuclideanSpace ℝ (Fin 2) => E 1 u) := hsmoothE.comp ppOneSlice_smooth
  have hE'1smooth : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : EuclideanSpace ℝ (Fin 2) => E' 1 u) := hsmoothE'.comp ppOneSlice_smooth
  -- ### the four derivative CLMs at the meet
  let A : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
    mfderiv (𝓡 2) (𝓡 4) (fun u : EuclideanSpace ℝ (Fin 2) => E 1 u) (ftU x)
  let B : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
    mfderiv (𝓡 2) (𝓡 4) (fun u : EuclideanSpace ℝ (Fin 2) => E' 1 u) (ftU x)
  let C : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
    mfderiv (𝓡 3) (𝓡 4) V (ftY x)
  let D : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
    mfderiv (𝓡 3) (𝓡 4) W (ftZ x)
  -- ### the chart-composed derivatives
  have hchartE : HasFDerivAt (fun u : EuclideanSpace ℝ (Fin 2) => chr p (E 1 u)) A (ftU x) := by
    have h := fderiv_chart_comp_hasFDerivAt (fun u : EuclideanSpace ℝ (Fin 2) => E 1 u)
      hE1smooth p (by rw [← hEp]; exact mem_chart_source _ _)
    have htc : tangentCoordChange (𝓡 4) (E 1 (ftU x)) p (E 1 (ftU x))
        = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 4)) := by
      rw [← hEp]; exact ppOnePpTc_self p
    rw [htc, ContinuousLinearMap.id_comp] at h
    exact h
  have hchartE' : HasFDerivAt (fun u : EuclideanSpace ℝ (Fin 2) => chr p' (E' 1 u)) B (ftU x) := by
    have h := fderiv_chart_comp_hasFDerivAt (fun u : EuclideanSpace ℝ (Fin 2) => E' 1 u)
      hE'1smooth p' (by rw [← hE'p]; exact mem_chart_source _ _)
    have htc : tangentCoordChange (𝓡 4) (E' 1 (ftU x)) p' (E' 1 (ftU x))
        = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 4)) := by
      rw [← hE'p]; exact ppOnePpTc_self p'
    rw [htc, ContinuousLinearMap.id_comp] at h
    exact h
  have hchartV : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 3) => chr p (V y)) C (ftY x) := by
    have h := fderiv_chart_comp_hasFDerivAt V hsmoothV p
      (by rw [← hx.2.1, ← hp]; exact mem_chart_source _ _)
    have htc : tangentCoordChange (𝓡 4) (V (ftY x)) p (V (ftY x))
        = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 4)) := by
      rw [hVp]; exact ppOnePpTc_self p
    rw [htc, ContinuousLinearMap.id_comp] at h
    exact h
  have hchartW : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 3) => chr p' (W z)) D (ftZ x) := by
    have h := fderiv_chart_comp_hasFDerivAt W hsmoothW p'
      (by rw [← hx.2.2, ← hp']; exact mem_chart_source _ _)
    have htc : tangentCoordChange (𝓡 4) (W (ftZ x)) p' (W (ftZ x))
        = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 4)) := by
      rw [hWp]; exact ppOnePpTc_self p'
    rw [htc, ContinuousLinearMap.id_comp] at h
    exact h
  -- ### the derivatives of the four blocks of the flat map
  have hftU' : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 9) => ftU z) ftUCLM x :=
    ftUCLM.hasFDerivAt.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun z => (ftUCLM_eq z).symm)
  have hftY' : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 9) => ftY z) ftYCLM x :=
    ftYCLM.hasFDerivAt.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun z => (ftYCLM_eq z).symm)
  have hftZ' : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 9) => ftZ z) ftZCLM x :=
    ftZCLM.hasFDerivAt.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun z => (ftZCLM_eq z).symm)
  have hEA : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 9) => chr p (E 1 (ftU z)))
      (A.comp ftUCLM) x := by
    have h := hchartE.comp x hftU'
    simpa only [Function.comp_def] using h
  have hEA' : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 9) => chr p' (E' 1 (ftU z)))
      (B.comp ftUCLM) x := by
    have h := hchartE'.comp x hftU'
    simpa only [Function.comp_def] using h
  have hVA : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 9) => chr p (V (ftY z)))
      (C.comp ftYCLM) x := by
    have h := hchartV.comp x hftY'
    simpa only [Function.comp_def] using h
  have hWA : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 9) => chr p' (W (ftZ z)))
      (D.comp ftZCLM) x := by
    have h := hchartW.comp x hftZ'
    simpa only [Function.comp_def] using h
  -- ### the flat derivative
  have hpup := TParity.hasFDerivAt_pUp (hEA.sub hVA) (hEA'.sub hWA)
  have hfun : (fun z : EuclideanSpace ℝ (Fin 9) =>
        TParity.pUp (chr p (E 1 (ftU z)) - chr p (V (ftY z)))
          (chr p' (E' 1 (ftU z)) - chr p' (W (ftZ z))))
      = fun z => ppDiff p p' E E' V W (ppOnePi1 z) := by
    funext z
    simp only [ppDiff, pair44_eq_pairUp, ppOne_ftS_pi1, ppOne_ftU_pi1, ppOne_ftY_pi1, ppOne_ftZ_pi1]
  let Λ : EuclideanSpace ℝ (Fin 9) →L[ℝ]
      (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)) :=
    ((A.comp ftUCLM) - (C.comp ftYCLM)).prod ((B.comp ftUCLM) - (D.comp ftZCLM))
  have hflatderiv : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 9) => ppDiff p p' E E' V W (ppOnePi1 z))
      (TParity.pUpCLM.comp Λ) x := by
    rw [← hfun]
    exact hpup
  -- ### the flat linear map is onto
  have hΛeq : Λ = (pairDiffTwoCLM A B C D).comp ppOneBlockProj := by
    refine ContinuousLinearMap.ext fun v => ?_
    rfl
  have hpair2 : Function.Surjective (pairDiffTwoCLM A B C D) :=
    surjective_pairDiffTwoCLM (by simp) A B C D hset hC hD
  have hΛsurj : Function.Surjective Λ := by
    rw [hΛeq]
    exact hpair2.comp ppOneBlockProj_surjective
  have hXsurj : Function.Surjective (TParity.pUpCLM.comp Λ) :=
    (PPIndep.surjective_comp_iff_of_bijective PPIndep.pUpCLM_bijective Λ).2 hΛsurj
  -- ### the derivative of the charted pair map along `rho9`
  have hQderiv : HasFDerivAt (ppDiff p p' E E' V W)
      (TParity.pUpCLM.comp ((PPIndep.ppA p p' E E' x).comp (PPIndep.ppFree E E' V W x))) x :=
    PPIndep.hasFDerivAt_ppDiff E E' V W hE9 hE'9 hV9 hW9 hx hres
  have hQdiff : DifferentiableAt ℝ (ppDiff p p' E E' V W) x := hQderiv.differentiableAt
  have hpi1x : ppOnePi1 x = x := ppOne_pi1_fixed x hx0
  have hQdiff' : DifferentiableAt ℝ (ppDiff p p' E E' V W) (ppOnePi1 x) := by
    rw [hpi1x]; exact hQdiff
  have hchain : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 9) => ppDiff p p' E E' V W (ppOnePi1 z))
      ((fderiv ℝ (ppDiff p p' E E' V W) x).comp rho9) x := by
    have h := hQdiff'.hasFDerivAt.comp x (ppOne_hasFDerivAt_pi1 x)
    rw [hpi1x] at h
    exact h
  have hkey : TParity.pUpCLM.comp Λ = (fderiv ℝ (ppDiff p p' E E' V W) x).comp rho9 :=
    hflatderiv.unique hchain
  -- ### the two clauses of `PPRegAt`
  refine ⟨?_, ?_⟩
  · intro w
    obtain ⟨q, hq⟩ := hXsurj w
    refine ⟨rho9 q, ?_⟩
    rw [hkey, ContinuousLinearMap.comp_apply] at hq
    exact hq
  · intro _
    refine ⟨0, ?_, ?_, ?_⟩
    · exact Or.inr hx0
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
      obtain ⟨q, hq⟩ := hXsurj w
      refine ⟨⟨rho9 q, rho9_zero q⟩, ?_⟩
      rw [hkey, ContinuousLinearMap.comp_apply] at hq
      exact hq

end

end Work.Drive
