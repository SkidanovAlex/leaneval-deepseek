import Mathlib

namespace Commons.Analysis.InnerProductSpace

open MeasureTheory

/-- The second derivative of a function composed with a linear isometry equivalence is the
second derivative at the image point, applied to the images of the two directions. -/
theorem fderiv_fderiv_comp_linearIsometryEquiv {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) (g : F → ℝ) (hg : ContDiff ℝ 2 g) (x v w : E) :
    fderiv ℝ (fderiv ℝ (fun y : E => g (e y))) x v w
      = fderiv ℝ (fderiv ℝ g) (e x) (e v) (e w) := by
  let L : E →L[ℝ] F := (e : E →L[ℝ] F)
  let Φ : (F →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) := (ContinuousLinearMap.compL ℝ E F ℝ).flip L
  change fderiv ℝ (fderiv ℝ (fun y : E => g (L y))) x v w
      = fderiv ℝ (fderiv ℝ g) (L x) (L v) (L w)
  have hg1 : Differentiable ℝ (fderiv ℝ g) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hg0 : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hL : Differentiable ℝ (fun y : E => L y) := ContinuousLinearMap.differentiable L
  have hΦ : ∀ M : F →L[ℝ] ℝ, Φ M = M.comp L := fun M => rfl
  have hφ : fderiv ℝ (fun y : E => g (L y)) = fun y : E => (fderiv ℝ g (L y)).comp L := by
    funext y
    rw [fderiv_fun_comp (f := L)]
    · rw [ContinuousLinearMap.fderiv]
    · exact hg0.differentiableAt
    · exact (ContinuousLinearMap.hasFDerivAt L).differentiableAt
  rw [hφ]
  have hA : fderiv ℝ (fun y : E => fderiv ℝ g (L y)) x
      = (fderiv ℝ (fderiv ℝ g) (L x)).comp L := by
    rw [fderiv_fun_comp (f := L)]
    · rw [ContinuousLinearMap.fderiv]
    · exact hg1.differentiableAt
    · exact (ContinuousLinearMap.hasFDerivAt L).differentiableAt
  have hB : fderiv ℝ (fun y : E => (fderiv ℝ g (L y)).comp L) x
      = Φ.comp (fderiv ℝ (fun y : E => fderiv ℝ g (L y)) x) := by
    have h1 : (fun y : E => (fderiv ℝ g (L y)).comp L)
        = fun y : E => Φ (fderiv ℝ g (L y)) := by
      funext y; rw [hΦ]
    rw [h1]
    rw [fderiv_fun_comp (f := fun y : E => fderiv ℝ g (L y)) (g := Φ)]
    · rw [ContinuousLinearMap.fderiv]
    · exact (ContinuousLinearMap.hasFDerivAt Φ).differentiableAt
    · exact (hg1.comp hL).differentiableAt
  rw [hB, hA]
  simp only [ContinuousLinearMap.comp_apply, hΦ]

end Commons.Analysis.InnerProductSpace
