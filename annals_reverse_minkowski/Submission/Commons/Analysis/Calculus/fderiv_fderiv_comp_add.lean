import Mathlib

namespace Commons.Analysis.Calculus

open MeasureTheory

theorem fderiv_fderiv_comp_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E → ℝ) (hg : ContDiff ℝ 2 g) (a x v w : E) :
    fderiv ℝ (fderiv ℝ (fun y : E => g (y + a))) x v w
      = fderiv ℝ (fderiv ℝ g) (x + a) v w := by
  have _ : ContDiff ℝ 2 g := hg
  have h1 : (fderiv ℝ (fun y : E => g (y + a))) = fun y : E => fderiv ℝ g (y + a) := by
    funext y
    exact fderiv_comp_add_right a
  rw [h1]
  rw [fderiv_comp_add_right a]

end Commons.Analysis.Calculus
