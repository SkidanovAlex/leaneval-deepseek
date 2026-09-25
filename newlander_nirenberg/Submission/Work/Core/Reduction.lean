import Submission.Work.Core.Defs

open LeanEval.Geometry.NewlanderNirenberg
open Set
open scoped ContDiff

namespace Submission

variable {n : ℕ}

/-- **From holomorphic functions to a holomorphic chart.**
If `u 0, …, u (n-1)` are `J`-holomorphic functions on an open set `V` (i.e. `du ∘ J = i·du`)
with everywhere invertible differential, then around any `x ∈ V` there is a chart of the
required form. -/
theorem exists_chart_of_holomorphic
    {U V : Set (E n)} (hV : IsOpen V) (hVU : V ⊆ U)
    (J : E n → E n →L[ℝ] E n) {x : E n} (hxV : x ∈ V)
    (u : Fin n → E n → ℂ)
    (hu : ∀ j : Fin n, ContDiffOn ℝ ∞ (u j) V)
    (hhol : ∀ j, ∀ y ∈ V, ∀ v : E n,
        fderiv ℝ (u j) y (J y v) = Complex.I * fderiv ℝ (u j) y v)
    (hinv : ∀ y ∈ V, Function.Bijective (fderiv ℝ (fun y : E n => fun j => u j y) y)) :
    ∃ φ : OpenPartialHomeomorph (E n) (EuclideanSpace ℂ (Fin n)),
      x ∈ φ.source ∧ φ.source ⊆ U ∧
      ContDiffOn ℝ ∞ (φ : E n → EuclideanSpace ℂ (Fin n)) φ.source ∧
      ContDiffOn ℝ ∞ (φ.symm : EuclideanSpace ℂ (Fin n) → E n) φ.target ∧
      ∀ y ∈ φ.source, ∀ v : E n,
        fderiv ℝ (φ : E n → EuclideanSpace ℂ (Fin n)) y (J y v)
          = Complex.I • fderiv ℝ (φ : E n → EuclideanSpace ℂ (Fin n)) y v := by
  set T : E n → (Fin n → ℂ) := fun y j => u j y with hT
  have hTsmooth : ContDiffOn ℝ ∞ T V := by
    rw [hT]; exact contDiffOn_pi.mpr hu
  have hTat : ∀ y ∈ V, ContDiffAt ℝ ∞ T y := fun y hy => hTsmooth.contDiffAt (hV.mem_nhds hy)
  have hTderiv : ∀ y ∈ V, fderiv ℝ T y =
      ContinuousLinearMap.pi (fun j => fderiv ℝ (u j) y) := by
    intro y hy
    rw [hT]
    exact fderiv_pi (fun j => ((hu j).contDiffAt (hV.mem_nhds hy)).differentiableAt (by simp))
  let F : E n → EuclideanSpace ℂ (Fin n) := fun y => ec n (T y)
  have hFsmooth : ContDiffOn ℝ ∞ F V := by
    have h1 : ContDiff ℝ ∞ (ecL n) := ContinuousLinearMap.contDiff (n := ∞) (ecL n)
    simpa [F, Function.comp_def] using h1.comp_contDiffOn hTsmooth
  have hFat : ContDiffAt ℝ ∞ F x := hFsmooth.contDiffAt (hV.mem_nhds hxV)
  have hFderivF : ∀ y ∈ V, fderiv ℝ F y = (ecL n).comp (fderiv ℝ T y) := by
    intro y hy
    have hdT : DifferentiableAt ℝ T y := (hTat y hy).differentiableAt (by simp)
    have hd : DifferentiableAt ℝ (ecL n) (T y) := (ContinuousLinearMap.hasFDerivAt (ecL n)).differentiableAt
    have hcomp := fderiv_comp y (f := T) (g := ecL n) hd hdT
    rw [ContinuousLinearMap.fderiv] at hcomp
    simpa [F, Function.comp_def] using hcomp
  have hFbij : ∀ y ∈ V, Function.Bijective (fderiv ℝ F y) := by
    intro y hy
    rw [hFderivF y hy, ContinuousLinearMap.coe_comp]
    exact (ecR n).bijective.comp (hinv y hy)
  let eF : E n ≃L[ℝ] EuclideanSpace ℂ (Fin n) :=
    ContinuousLinearEquiv.ofBijective (fderiv ℝ F x)
      (LinearMap.ker_eq_bot.mpr (hFbij x hxV).1) (LinearMap.range_eq_top.mpr (hFbij x hxV).2)
  have heF : (eF : E n →L[ℝ] EuclideanSpace ℂ (Fin n)) = fderiv ℝ F x :=
    ContinuousLinearEquiv.coe_ofBijective _ _ _
  have hFfderiv : HasFDerivAt F (eF : E n →L[ℝ] EuclideanSpace ℂ (Fin n)) x := by
    rw [heF]
    exact (hFat.differentiableAt (by simp)).hasFDerivAt
  let φ₀ : OpenPartialHomeomorph (E n) (EuclideanSpace ℂ (Fin n)) :=
    hFat.toOpenPartialHomeomorph F hFfderiv (by simp)
  have hcoe₀ : (φ₀ : E n → EuclideanSpace ℂ (Fin n)) = F :=
    ContDiffAt.toOpenPartialHomeomorph_coe _ _ _
  have hxφ₀ : x ∈ φ₀.source :=
    hFat.mem_toOpenPartialHomeomorph_source hFfderiv (by simp)
  obtain ⟨ε, hεpos, hεV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hxV)
  let φ : OpenPartialHomeomorph (E n) (EuclideanSpace ℂ (Fin n)) :=
    φ₀.restrOpen (Metric.ball x ε) Metric.isOpen_ball
  have hcoe : (φ : E n → EuclideanSpace ℂ (Fin n)) = F := by
    rw [OpenPartialHomeomorph.coe_restrOpen, hcoe₀]
  have hsource : φ.source ⊆ V := by
    intro y hy
    rw [OpenPartialHomeomorph.restrOpen_source] at hy
    exact hεV hy.2
  refine ⟨φ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.restrOpen_source]
    exact ⟨hxφ₀, Metric.mem_ball_self hεpos⟩
  · intro y hy
    exact hVU (hsource hy)
  · have h1 : ContDiffOn ℝ ∞ F φ.source := hFsmooth.mono hsource
    simpa [hcoe] using h1
  · intro a ha
    have hb_src : φ.symm a ∈ φ.source := φ.map_target ha
    have hbV : φ.symm a ∈ V := hsource hb_src
    have hbF : Function.Bijective (fderiv ℝ F (φ.symm a)) := hFbij _ hbV
    let eFb : E n ≃L[ℝ] EuclideanSpace ℂ (Fin n) :=
      ContinuousLinearEquiv.ofBijective (fderiv ℝ F (φ.symm a))
        (LinearMap.ker_eq_bot.mpr hbF.1) (LinearMap.range_eq_top.mpr hbF.2)
    have heFb : (eFb : E n →L[ℝ] EuclideanSpace ℂ (Fin n)) = fderiv ℝ F (φ.symm a) :=
      ContinuousLinearEquiv.coe_ofBijective _ _ _
    have hfderiv_φ : HasFDerivAt (φ : E n → EuclideanSpace ℂ (Fin n))
        (eFb : E n →L[ℝ] EuclideanSpace ℂ (Fin n)) (φ.symm a) := by
      rw [heFb]
      have hFb : HasFDerivAt F (fderiv ℝ F (φ.symm a)) (φ.symm a) :=
        (((hFsmooth.contDiffAt (hV.mem_nhds hbV)).differentiableAt (by simp)).hasFDerivAt)
      refine hFb.congr_of_eventuallyEq ?_
      filter_upwards [φ.open_source.mem_nhds hb_src] with y hy
      rw [← hcoe]
    have hcont_φ : ContDiffAt ℝ ∞ (φ : E n → EuclideanSpace ℂ (Fin n)) (φ.symm a) := by
      have hFb : ContDiffAt ℝ ∞ F (φ.symm a) := hFsmooth.contDiffAt (hV.mem_nhds hbV)
      refine hFb.congr_of_eventuallyEq ?_
      filter_upwards [φ.open_source.mem_nhds hb_src] with y hy
      rw [← hcoe]
    exact (φ.contDiffAt_symm ha hfderiv_φ hcont_φ).contDiffWithinAt
  · intro y hy v
    rw [OpenPartialHomeomorph.restrOpen_source] at hy
    have hyV : y ∈ V := hεV hy.2
    rw [hcoe, hFderivF y hyV, ContinuousLinearMap.comp_apply, hTderiv y hyV,
      ContinuousLinearMap.comp_apply]
    have h1 : (ContinuousLinearMap.pi (fun j => fderiv ℝ (u j) y)) (J y v)
        = Complex.I • (fun j => fderiv ℝ (u j) y v) := by
      funext j
      rw [ContinuousLinearMap.pi_apply, Pi.smul_apply]
      exact hhol j y hyV v
    have h2 : (ContinuousLinearMap.pi (fun j => fderiv ℝ (u j) y)) v
        = (fun j => fderiv ℝ (u j) y v) := by
      funext j
      rw [ContinuousLinearMap.pi_apply]
    rw [h1, h2, ecL_smul]



end Submission
