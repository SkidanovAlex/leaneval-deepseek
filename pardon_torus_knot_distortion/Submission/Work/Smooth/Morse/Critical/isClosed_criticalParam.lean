import Mathlib
import Submission.Work.Smooth.Morse.Defs

namespace Work.Smooth.Morse.Critical

open Work.Smooth.Morse

/-- The set of critical points of `pullback ψ g` is the preimage of `{0}` under the (continuous)
derivative of `pullback ψ g`. -/
theorem criticalParam_eq_preimage_zero (ψ : Submission.Diffeo) (g : LeanEval.KnotTheory.PardonDistortion.R3 → ℝ) :
    Work.Smooth.Morse.criticalParam ψ g = (fderiv ℝ (pullback ψ g)) ⁻¹' {0} := rfl

/-- The derivative of a `C¹` function is continuous. -/
theorem continuous_fderiv_pullback (ψ : Submission.Diffeo) {g : LeanEval.KnotTheory.PardonDistortion.R3 → ℝ}
    (hg : ContDiff ℝ 1 g) : Continuous (fderiv ℝ (pullback ψ g)) :=
  (pullback_contDiff_one ψ hg).continuous_fderiv one_ne_zero

theorem isClosed_criticalParam (ψ : Submission.Diffeo) {g : LeanEval.KnotTheory.PardonDistortion.R3 → ℝ} (hg : ContDiff ℝ 1 g) : IsClosed (Work.Smooth.Morse.criticalParam ψ g) := by
  rw [criticalParam_eq_preimage_zero]
  exact isClosed_singleton.preimage (continuous_fderiv_pullback ψ hg)

end Work.Smooth.Morse.Critical
