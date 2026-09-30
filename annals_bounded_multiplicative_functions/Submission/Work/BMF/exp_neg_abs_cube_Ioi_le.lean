import Mathlib
import Submission.Work.BMF.integrable_exp_neg_abs_cube

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedVariables false

namespace Work.BMF

open MeasureTheory Set

/-- For `y ≥ 0`, the integral of `w ↦ exp(-|w|³)` over `(-y, ∞)` is at most twice its integral
over `(0, ∞)`.

The integrand `G w = exp(-|w|³) = f |w|` with `f t = exp(-t³)` is nonnegative, so restricting it
to the half-line `(-y, ∞) ⊆ ℝ` can only decrease the integral; and over all of `ℝ` the substitution
`w ↦ |w|` (`integral_comp_abs`) gives exactly twice the integral over `(0, ∞)`. -/
lemma exp_neg_abs_cube_Ioi_le (y : ℝ) (hy : 0 ≤ y) :
    ∫ w in Set.Ioi (-y), Real.exp (-(|w| ^ 3)) ≤ 2 * ∫ w in Set.Ioi (0 : ℝ), Real.exp (-(w ^ 3)) := by
  have hle : ∫ w in Set.Ioi (-y), Real.exp (-(|w| ^ 3)) ≤ ∫ w, Real.exp (-(|w| ^ 3)) := by
    apply setIntegral_le_integral integrable_exp_neg_abs_cube
    filter_upwards with w
    exact (Real.exp_pos _).le
  calc ∫ w in Set.Ioi (-y), Real.exp (-(|w| ^ 3))
      ≤ ∫ w, Real.exp (-(|w| ^ 3)) := hle
    _ = 2 * ∫ w in Set.Ioi (0 : ℝ), Real.exp (-(w ^ 3)) := by
        simpa using integral_comp_abs (f := fun t : ℝ => Real.exp (-(t ^ 3)))

end Work.BMF
