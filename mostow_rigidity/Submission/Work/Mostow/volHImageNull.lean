import Mathlib
import Submission.Work.Mostow.VolDefs

/-!
# A `C¹` map of the chart sends `volH`-null sets to `volH`-null sets

The hyperbolic volume `volH n` has a density `hdens` with respect to Lebesgue measure on the
chart `E n` which is everywhere positive and finite on compact sets (`Work.Mostow.hdens_pos`),
hence has exactly the same null sets as Lebesgue measure (`Work.Mostow.volHNull`). Mathlib's
change-of-variables theory (`addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`)
says that a map differentiable on a Lebesgue-null set `N` has an image `F '' N` which is again
Lebesgue-null. Composing the two gives the statement.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

/-- A `C¹` self-map of the chart `E n` maps `volH n`-null sets to `volH n`-null sets. -/
theorem volHImageNull (n : ℕ) {F : E n → E n} (hF : ContDiff ℝ 1 F) {N : Set (E n)}
    (hN : volH n N = 0) : volH n (F '' N) = 0 := by
  rw [volHNull n] at hN ⊢
  exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
    ((hF.differentiable (by norm_num)).differentiableOn) hN

end Work.Mostow
