import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BSKinetic.IterKernelAux

/-- The windowed mode form `winModeForm χ F u = (2π)⁻³∫_p F‖p‖·‖kinFT (χ·u) p‖²` depends on
`χ` and `u` only through the product `χ·u`: if `χ₁ x * u₁ x = χ₂ x * u₂ x` for every `x`, then
`winModeForm χ₁ F u₁ = winModeForm χ₂ F u₂`. -/
lemma winModeForm_congr_mul {F : ℝ → ℝ} {χ₁ χ₂ u₁ u₂ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hprod : ∀ x, χ₁ x * u₁ x = χ₂ x * u₂ x) :
    Submission.BoseGases.winModeForm χ₁ F u₁ = Submission.BoseGases.winModeForm χ₂ F u₂ := by
  have h : (fun y => (χ₁ y : ℂ) * u₁ y) = (fun y => (χ₂ y : ℂ) * u₂ y) := by
    funext y
    exact_mod_cast hprod y
  unfold Submission.BoseGases.winModeForm
  rw [h]

end Work.BSKinetic.IterKernelAux
