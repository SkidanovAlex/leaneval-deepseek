import Mathlib
import Submission.Work.Diff.STE.Lead.JointSmoothKit
import Submission.Work.Diff.STE.Man.chartNonlin_eq_pPhiJet
import Submission.Work.Diff.STE.B3.TransportDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Work.Diff.STE.Flat Work.Diff.STE.Man Work.Diff.STE.DeTurck Work.Diff.EXT Filter
open scoped Manifold ContDiff Bundle Topology BigOperators Matrix
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.STE.Lead

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-- The `(i,j)`-th entry of a real matrix, as a continuous linear functional. -/
lemma ext_matEntryCLM_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E] (i j : Fin (Module.finrank ℝ E))
    (A : Work.Diff.EXT.MatE (E := E)) :
    Work.Diff.EXT.matEntryCLM (E := E) i j A = A i j := by
  simp only [Work.Diff.EXT.matEntryCLM, LinearMap.coe_toContinuousLinearMap',
    LinearMap.comp_apply, LinearMap.proj_apply]

/-- **`ofRealMat` as a continuous linear map** (the inverse direction of
`Work.Diff.STE.Man.reMatECLM`). -/
noncomputable def ofRealMatCLM {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E] :
    Work.Diff.EXT.MatE (E := E) →L[ℝ] Work.Diff.STE.Flat.MatC (Module.finrank ℝ E) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j =>
    Complex.ofRealCLM.comp (Work.Diff.EXT.matEntryCLM (E := E) i j)

@[simp] lemma ofRealMatCLM_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E] (A : Work.Diff.EXT.MatE (E := E)) :
    ofRealMatCLM (E := E) A = Work.Diff.STE.Man.ofRealMat A := by
  funext i j
  simp only [ofRealMatCLM, ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply,
    ext_matEntryCLM_apply, Complex.ofRealCLM_apply, Work.Diff.STE.Man.ofRealMat_apply]

/-! ## The chart nonlinearity with an arbitrary background

`Work.Diff.STE.Man.chartNonlin_eq_pPhiJet` identifies `chartNonlin bg (z, jetM (u t) z)` with
`pPhiJet G g₀ x₀ (chartCoordSymm I x₀ z)` in the special case that the background `bg` is the
*periodisation* `chartDatumR g₀ x₀ r hr` of the chart matrix of `g₀`.  The only property of the
background that the argument uses is that it agrees with `chartMatFun g₀ x₀ ∘ chartCoordSymm`
*eventually* near `z` (and is smooth there); the statement below is that generic form, which is
what the generalised chart-`PDE` statement `Work.Diff.STE.Lead.chartMat_solves_chartNonlin_gen`
needs. -/

/-- **`chartNonlin` at a background which agrees with the chart matrix of `g₀` near `z` is
`pPhiJet`.** -/
theorem chartNonlin_eq_pPhiJet_of_eventuallyEq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (g₀ G : Submission.Diff.SMet I M) (x₀ : M)
    (u : ℝ → Torus (dim E)) (t : ℝ) (z : Fin (dim E) → ℝ)
    (bg : (Fin (dim E) → ℝ) → MatE (E := E))
    (hbg : bg =ᶠ[nhds z] fun z' => chartMatFun g₀ x₀ (chartCoordSymm I x₀ z'))
    (hg₀ : ContDiffAt ℝ (⊤ : ℕ∞) (chartMatFun g₀ x₀) (chartCoordSymm I x₀ z))
    (hGsm : ContDiffAt ℝ (⊤ : ℕ∞) (chartMatFun G x₀) (chartCoordSymm I x₀ z))
    (hG : (fun z' => reMatE (u t z'))
      =ᶠ[nhds z] fun z' => chartMatFun G x₀ (chartCoordSymm I x₀ z'))
    (hu : ContDiffAt ℝ (⊤ : ℕ∞) (u t) z)
    (hure : ∀ᶠ z' in nhds z, ∀ i j, (u t z' i j).im = 0)
    (husy : ∀ᶠ z' in nhds z, ∀ i j, u t z' i j = u t z' j i)
    (hdet : (Matrix.of (reMatE (u t z))).det ≠ 0) :
    chartNonlin (E := E) bg (z, jetM (u t) z)
      = ofRealMat (pPhiJet G g₀ x₀ (chartCoordSymm I x₀ z)) := by
  obtain ⟨hb1, hb2, hb3⟩ :=
    dpd_of_eventuallyEq_comp (I := I) x₀ (chartMatFun g₀ x₀) z bg hg₀ hbg
  obtain ⟨hG1, hG2, hG3⟩ :=
    dpd_of_eventuallyEq_comp (I := I) x₀ (chartMatFun G x₀) z
      (fun z' => reMatE (u t z')) hGsm hG
  have hA : ∀ i j, u t z i j = u t z j i := fun i j => husy.self_of_nhds i j
  have hL : ∀ c i j, pdM c (u t) z i j = pdM c (u t) z j i :=
    fun c i j => pdM_symm husy c i j
  have hB1 : ∀ c d, pdM c (pdM d (u t)) z = pdM d (pdM c (u t)) z :=
    fun c d => pdM_pdM_comm hu c d
  have hB2 : ∀ c d i j, pdM c (pdM d (u t)) z i j = pdM c (pdM d (u t)) z j i :=
    fun c d i j => pdM_pdM_symm husy c d i j
  have hBim : ∀ c d i j, (pdM c (pdM d (u t)) z i j).im = 0 :=
    fun c d i j => im_pdM_pdM_eq_zero hu hure c d i j
  have hmain := chartNonlin_eq_pPhi (E := E) bg z (u t z)
    (fun c => pdM c (u t) z) (fun c d => pdM c (pdM d (u t)) z) hA hL hB1 hB2 hBim hdet
  have hjet : jetM (u t) z
      = ((u t z), (fun c => pdM c (u t) z), fun c d => pdM c (pdM d (u t)) z) := rfl
  rw [hjet, hmain]
  have e1 : bg z = (DeTurck.chartJet g₀ x₀ (chartCoordSymm I x₀ z)).1 := hb1
  have e2 : linMatOf (E := E) (fun c => dpd (E := E) c bg z)
      = (DeTurck.chartJet g₀ x₀ (chartCoordSymm I x₀ z)).2.1 := by
    refine clm_ext_bB (fun c => ?_)
    rw [linMatOf_bB]
    rw [hb2 c]
    rfl
  have e3 : bilMatOf (E := E) (fun c d => dpd (E := E) c (dpd (E := E) d bg) z)
      = (DeTurck.chartJet g₀ x₀ (chartCoordSymm I x₀ z)).2.2 := by
    refine bilin_ext_bB (fun c d => ?_)
    rw [bilMatOf_bB]
    rw [hb3 c d]
    rfl
  have e4 : reMatE (u t z) = (DeTurck.chartJet G x₀ (chartCoordSymm I x₀ z)).1 := hG1
  have e5 : linMatOf (E := E) (fun c => reMatE (pdM c (u t) z))
      = (DeTurck.chartJet G x₀ (chartCoordSymm I x₀ z)).2.1 := by
    refine clm_ext_bB (fun c => ?_)
    rw [linMatOf_bB]
    rw [show (DeTurck.chartJet G x₀ (chartCoordSymm I x₀ z)).2.1 (bB (E := E) c)
        = fderiv ℝ (chartMatFun G x₀) (chartCoordSymm I x₀ z) (bB (E := E) c) from rfl,
      ← hG2 c]
    exact (dpd_reMatE (u t) z (hu.differentiableAt (by simp)) c).symm
  have e6 : bilMatOf (E := E) (fun c d => reMatE (pdM c (pdM d (u t)) z))
      = (DeTurck.chartJet G x₀ (chartCoordSymm I x₀ z)).2.2 := by
    refine bilin_ext_bB (fun c d => ?_)
    rw [bilMatOf_bB]
    rw [show (DeTurck.chartJet G x₀ (chartCoordSymm I x₀ z)).2.2 (bB (E := E) c) (bB (E := E) d)
        = (fderiv ℝ (fderiv ℝ (chartMatFun G x₀)) (chartCoordSymm I x₀ z))
            (bB (E := E) c) (bB (E := E) d) from rfl,
      ← hG3 c d]
    exact (dpd_dpd_reMatE (u t) z hu c d).symm
  apply congrArg ofRealMat
  rw [e1, e2, e3, e4, e5, e6]
  rfl

section Aux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-- **The chart matrix of a positive definite section is the chart matrix of its metric.** -/
lemma chartMatC_eq_ofRealMat_chartMatFun
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
    (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < h x v v)
    (hsm : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
    (j : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ) :
    chartMatC (I := I) (M := M) D h j z
      = ofRealMat (chartMatFun (I := I) (M := M)
          (Work.Diff.STE.D.smetOf (I := I) h hsym hpos hsm) (D.x₀ j)
          (chartCoordSymm I (D.x₀ j) z)) := by
  funext a b
  simp only [chartMatC, Work.Diff.STE.B3.Gf, Work.Diff.STE.Man.ofRealMat_apply,
    Work.Diff.EXT.chartMatFun, Work.Diff.STE.D.chartMatOf_apply, Work.Diff.STE.D.smetOf_inner,
    Work.Diff.STE.B3.yf, flatToE_eq_chartCoordSymm]

end Aux

theorem chartMat_solves_chartNonlin_gen
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (hLC : Submission.Diff.LCSmooth I M)
    (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) g₀.inner)
    (τ : ℝ) (hτ : 0 < τ) (U : ℝ → Work.Diff.STE.Bil (I := I) (M := M))
    (hsym : ∀ (t : ℝ) (x : M) (u v : TangentSpace I x), (U t) x u v = (U t) x v u)
    (hpos : ∀ (t : ℝ) (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < (U t) x v v)
    (hsm : ∀ t : ℝ, Work.Diff.STE.D.ChartData (I := I) (M := M) (U t))
    (heq : ∀ t ∈ Set.Ico (0 : ℝ) τ, ∀ (x : M) (u v : TangentSpace I x),
      HasDerivWithinAt (fun s : ℝ => (U s) x u v)
        ((Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ (U t) (hsym t) (hpos t) (hsm t)) x u v)
        (Set.Ico (0 : ℝ) τ) t)
    (i : ι₀) (c : Fin (Module.finrank ℝ E) → ℝ) (ρ ρ' : ℝ)
    (hρ : 0 < ρ) (hρ' : ρ < ρ') (hball : ‖c‖ + ρ' < 2 * D.σ i)
    (bg : (Fin (Module.finrank ℝ E) → ℝ) → Work.Diff.EXT.MatE (E := E))
    (hbgsm : ContDiff ℝ (⊤ : ℕ∞) bg)
    (hbg : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z - c‖ < ρ' →
      bg z = Work.Diff.STE.Man.flatChartMat (I := I) g₀ (D.x₀ i) z) :
    ∀ t ∈ Set.Ico (0 : ℝ) τ, ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z - c‖ < ρ →
      HasDerivWithinAt
        (fun s : ℝ => Work.Diff.STE.Lead.chartMatC (I := I) (M := M) D (U s) i z)
        (Work.Diff.STE.Man.chartNonlin (E := E) bg
          (z, Work.Diff.STE.Flat.jetM (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            Work.Diff.STE.Lead.chartMatC (I := I) (M := M) D (U t) i y) z))
        (Set.Ico (0 : ℝ) τ) t := by
  intro t ht z hz
  -- ######################## radii
  have hzρ' : ‖z - c‖ < ρ' := lt_trans hz hρ'
  have hz2 : ‖z‖ < 2 * D.σ i := by
    have h1 : ‖z‖ ≤ ‖c‖ + ‖z - c‖ := by simpa using norm_add_le c (z - c)
    linarith
  have hytar : chartCoordSymm I (D.x₀ i) z ∈ (extChartAt I (D.x₀ i)).target := by
    rw [← flatToE_eq_chartCoordSymm]
    exact D.htarget i z hz2.le
  -- ######################## the chart coordinate is smooth
  have hcc : ContDiffAt ℝ (⊤ : ℕ∞) (chartCoordSymm I (D.x₀ i)) z := by
    rw [chartCoordSymm_eq]
    exact contDiffAt_const.add ((chartLin (E := E)).contDiff.contDiffAt)
  -- ######################## smoothness of the chart matrices
  have hg₀sm : ContDiffAt ℝ (⊤ : ℕ∞) (chartMatFun (I := I) (M := M) g₀ (D.x₀ i))
      (chartCoordSymm I (D.x₀ i) z) :=
    Work.Diff.EXT.kz_contDiffAt_chartMatFun (I := I) g₀ (D.x₀ i) hytar
  have hGsm : ContDiffAt ℝ (⊤ : ℕ∞) (chartMatFun (I := I) (M := M)
      (Work.Diff.STE.D.smetOf (I := I) (U t) (hsym t) (hpos t) (hsm t)) (D.x₀ i))
      (chartCoordSymm I (D.x₀ i) z) :=
    Work.Diff.EXT.kz_contDiffAt_chartMatFun (I := I)
      (Work.Diff.STE.D.smetOf (I := I) (U t) (hsym t) (hpos t) (hsm t)) (D.x₀ i) hytar
  have hu : ContDiffAt ℝ (⊤ : ℕ∞) (chartMatC (I := I) (M := M) D (U t) i) z := by
    have h3 := (ofRealMatCLM (E := E)).contDiff.contDiffAt.comp z (hGsm.comp z hcc)
    have h2 : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun y : Fin (Module.finrank ℝ E) → ℝ => ofRealMat (chartMatFun (I := I) (M := M)
          (Work.Diff.STE.D.smetOf (I := I) (U t) (hsym t) (hpos t) (hsm t)) (D.x₀ i)
          (chartCoordSymm I (D.x₀ i) y))) z := by
      refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
      simp only [Function.comp_apply, ofRealMatCLM_apply]
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    exact chartMatC_eq_ofRealMat_chartMatFun (I := I) (M := M) D (U t) (hsym t) (hpos t)
      (hsm t) i y
  -- ######################## the background agrees with the chart matrix of `g₀`
  have hbgev : bg =ᶠ[nhds z] fun z' => chartMatFun (I := I) (M := M) g₀ (D.x₀ i)
      (chartCoordSymm I (D.x₀ i) z') := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (by
      rw [Metric.mem_ball, dist_eq_norm]; exact hzρ')] with z' hz'
    rw [hbg z' (by rw [Metric.mem_ball, dist_eq_norm] at hz'; exact hz')]
    rfl
  -- ######################## reality and symmetry of the unknown
  have hure : ∀ᶠ z' in nhds z, ∀ j k : Fin (Module.finrank ℝ E),
      (chartMatC (I := I) (M := M) D (U t) i z' j k).im = 0 := by
    filter_upwards with z' j k
    simp only [chartMatC, Work.Diff.STE.Man.ofRealMat_apply, Complex.ofReal_im]
  have husy : ∀ᶠ z' in nhds z, ∀ j k : Fin (Module.finrank ℝ E),
      chartMatC (I := I) (M := M) D (U t) i z' j k
        = chartMatC (I := I) (M := M) D (U t) i z' k j := by
    filter_upwards with z' j k
    simp only [chartMatC, Work.Diff.STE.Man.ofRealMat_apply, Complex.ofReal_inj]
    simp only [Work.Diff.STE.B3.Gf, Work.Diff.STE.D.chartMatOf_apply]
    exact hsym t _ _ _
  have hdet : (Matrix.of (reMatE (chartMatC (I := I) (M := M) D (U t) i z))).det ≠ 0 := by
    rw [reMatE_chartMatC]
    exact det_Gf_ne_zero (I := I) (M := M) D (U t) (hsym t) (hpos t) i hz2.le
  have hGev : (fun z' : Fin (Module.finrank ℝ E) → ℝ =>
        reMatE (chartMatC (I := I) (M := M) D (U t) i z'))
      =ᶠ[nhds z] fun z' => chartMatFun (I := I) (M := M)
        (Work.Diff.STE.D.smetOf (I := I) (U t) (hsym t) (hpos t) (hsm t)) (D.x₀ i)
        (chartCoordSymm I (D.x₀ i) z') := by
    filter_upwards with z'
    rw [chartMatC_eq_ofRealMat_chartMatFun (I := I) (M := M) D (U t) (hsym t) (hpos t)
      (hsm t) i z']
    rfl
  -- ######################## the derivative from the DeTurck equation
  have hderiv : HasDerivWithinAt
      (fun s : ℝ => ofRealMat (chartMatFun (I := I) (M := M)
        (Work.Diff.STE.D.smetOf (I := I) (U s) (hsym s) (hpos s) (hsm s)) (D.x₀ i)
        (chartCoordSymm I (D.x₀ i) z)))
      (ofRealMat (pPhiJet (Work.Diff.STE.D.smetOf (I := I) (U t) (hsym t) (hpos t) (hsm t))
        g₀ (D.x₀ i) (chartCoordSymm I (D.x₀ i) z)))
      (Set.Ico (0 : ℝ) τ) t := by
    rw [hasDerivWithinAt_pi]
    intro a
    rw [hasDerivWithinAt_pi]
    intro b
    have hentry : HasDerivWithinAt
        (fun s : ℝ => chartMatFun (I := I) (M := M)
          (Work.Diff.STE.D.smetOf (I := I) (U s) (hsym s) (hpos s) (hsm s)) (D.x₀ i)
          (chartCoordSymm I (D.x₀ i) z) a b)
        (pPhiJet (Work.Diff.STE.D.smetOf (I := I) (U t) (hsym t) (hpos t) (hsm t))
          g₀ (D.x₀ i) (chartCoordSymm I (D.x₀ i) z) a b)
        (Set.Ico (0 : ℝ) τ) t := by
      have hp := heq t ht ((extChartAt I (D.x₀ i)).symm (chartCoordSymm I (D.x₀ i) z))
        (Work.Diff.GE.cFrame (I := I) (D.x₀ i) a
          ((extChartAt I (D.x₀ i)).symm (chartCoordSymm I (D.x₀ i) z)))
        (Work.Diff.GE.cFrame (I := I) (D.x₀ i) b
          ((extChartAt I (D.x₀ i)).symm (chartCoordSymm I (D.x₀ i) z)))
      simpa only [Work.Diff.EXT.chartMatFun, Work.Diff.STE.DeTurck.chartDeTurckMat,
        Work.Diff.STE.D.smetOf_inner, Work.Diff.GE.cFrame_apply, Work.Diff.GE.cBasis,
        Work.Diff.EXT.bB, Work.Diff.STE.D.deTurckSec_apply,
        Work.Diff.STE.D.psi.pPhiJet_eq_chartDeTurckMat (I := I) (M := M)
          (Work.Diff.STE.D.smetOf (I := I) (U t) (hsym t) (hpos t) (hsm t)) g₀ (D.x₀ i) hytar]
        using hp
    have h4 := HasFDerivAt.comp_hasDerivWithinAt t Complex.ofRealCLM.hasFDerivAt hentry
    refine h4.congr (fun x _ => ?_) ?_
    · simp only [Function.comp_apply, Complex.ofRealCLM_apply, Work.Diff.STE.Man.ofRealMat_apply]
    · simp only [Function.comp_apply, Complex.ofRealCLM_apply, Work.Diff.STE.Man.ofRealMat_apply]
  -- ######################## assembly
  have hRHS : chartNonlin (E := E) bg
      (z, jetM (fun y : Fin (Module.finrank ℝ E) → ℝ =>
        chartMatC (I := I) (M := M) D (U t) i y) z)
      = ofRealMat (pPhiJet (Work.Diff.STE.D.smetOf (I := I) (U t) (hsym t) (hpos t) (hsm t))
          g₀ (D.x₀ i) (chartCoordSymm I (D.x₀ i) z)) :=
    chartNonlin_eq_pPhiJet_of_eventuallyEq (I := I) (M := M) g₀
      (Work.Diff.STE.D.smetOf (I := I) (U t) (hsym t) (hpos t) (hsm t)) (D.x₀ i)
      (fun (_ : ℝ) (y : Fin (Module.finrank ℝ E) → ℝ) =>
        chartMatC (I := I) (M := M) D (U t) i y)
      t z bg hbgev hg₀sm hGsm hGev hu hure husy hdet
  rw [show (fun s : ℝ => Work.Diff.STE.Lead.chartMatC (I := I) (M := M) D (U s) i z)
      = fun s : ℝ => ofRealMat (chartMatFun (I := I) (M := M)
          (Work.Diff.STE.D.smetOf (I := I) (U s) (hsym s) (hpos s) (hsm s)) (D.x₀ i)
          (chartCoordSymm I (D.x₀ i) z)) from funext fun s =>
        chartMatC_eq_ofRealMat_chartMatFun (I := I) (M := M) D (U s) (hsym s) (hpos s)
          (hsm s) i z]
  rw [hRHS]
  exact hderiv

end Work.Diff.STE.Lead
