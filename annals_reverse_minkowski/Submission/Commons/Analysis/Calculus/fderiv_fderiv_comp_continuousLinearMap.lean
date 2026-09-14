import Mathlib

namespace Commons.Analysis.Calculus

open MeasureTheory

/-- The second derivative of `g ∘ L`, where `L` is a continuous linear map and `g` is `C²`,
evaluated at `(v, w)`, equals the second derivative of `g` at `L x` evaluated at
`(L v, L w)`. -/
theorem fderiv_fderiv_comp_continuousLinearMap {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (g : F → ℝ) (hg : ContDiff ℝ 2 g) (x v w : E) :
    fderiv ℝ (fderiv ℝ (fun y : E => g (L y))) x v w
      = fderiv ℝ (fderiv ℝ g) (L x) (L v) (L w) := by
  -- Rewrite both sides using the identification of second derivatives with `iteratedFDeriv`.
  have h1 : (iteratedFDeriv ℝ 2 (fun y : E => g (L y)) x) ![v, w]
      = fderiv ℝ (fderiv ℝ (fun y : E => g (L y))) x v w := by
    simpa using iteratedFDeriv_two_apply (𝕜 := ℝ) (f := fun y : E => g (L y)) x ![v, w]
  have h2 : (iteratedFDeriv ℝ 2 g (L x)) ![L v, L w]
      = fderiv ℝ (fderiv ℝ g) (L x) (L v) (L w) := by
    simpa using iteratedFDeriv_two_apply (𝕜 := ℝ) (f := g) (z := L x) ![L v, L w]
  rw [← h1, ← h2]
  -- Apply the chain rule for iterated derivatives of a continuous linear map.
  have h := ContinuousLinearMap.iteratedFDeriv_comp_right (𝕜 := ℝ) L hg x (i := 2) (by norm_num)
  have h' : iteratedFDeriv ℝ 2 (fun y : E => g (L y)) x
      = (iteratedFDeriv ℝ 2 g (L x)).compContinuousLinearMap (fun _ => L) := by
    simpa only [Function.comp_def] using h
  rw [h']
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  ext i
  fin_cases i <;> simp

end Commons.Analysis.Calculus
