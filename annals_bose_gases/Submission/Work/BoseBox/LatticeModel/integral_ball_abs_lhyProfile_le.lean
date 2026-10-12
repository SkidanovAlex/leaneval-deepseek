import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBox.LatticeModel.integrableOn_radial_ball_bound
import Submission.Work.BoseBox.LatticeModel.radial_ball_bound_value
import Submission.Work.BoseBox.LatticeModel.radial_integral_corollaries
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.unusedVariables false

namespace Work.BoseBox.LatticeModel

open MeasureTheory Set
open scoped Real

theorem integral_ball_abs_lhyProfile_le {c : ℝ} (hc : 0 < c) {A : ℝ} (hA : 0 ≤ A)
    (h1 : ∀ r : ℝ, 0 ≤ r → |lhyProfile c r| ≤ c + c ^ 2 / (2 * r ^ 2)) :
    (∫ x in {x : Fin 3 → ℝ | Submission.BoseGases.eucNorm3 x ≤ A},
        |lhyProfile c (Submission.BoseGases.eucNorm3 x)|)
      ≤ 4 * Real.pi * (c * A ^ 3 / 3 + c ^ 2 * A / 2) := by
  -- Reduce the ball integral to a one-dimensional radial integral in the radius.
  rw [show (∫ x in {x : Fin 3 → ℝ | Submission.BoseGases.eucNorm3 x ≤ A},
        |lhyProfile c (Submission.BoseGases.eucNorm3 x)|)
      = (∫ x in {x : Fin 3 → ℝ | Submission.BoseGases.eucNorm3 x ∈ Set.Iic A},
          (fun r : ℝ => |lhyProfile c r|) (Submission.BoseGases.eucNorm3 x)) from rfl]
  rw [setIntegral_eucNorm3_eq (Set.Iic A) measurableSet_Iic (fun r : ℝ => |lhyProfile c r|)]
  -- Compare the radial integrand with the model bound `r² · 1_{r≤A}(c + c²/(2r²))`.
  have hkey : (∫ r in Set.Ioi (0 : ℝ),
        r ^ 2 * (Set.Iic A).indicator (fun r : ℝ => |lhyProfile c r|) r)
      ≤ c * A ^ 3 / 3 + c ^ 2 * A / 2 := by
    rw [← radial_ball_bound_value hA]
    apply integral_mono_of_nonneg _ (integrableOn_radial_ball_bound c A) _
    · -- the left integrand is nonnegative
      refine ae_restrict_of_forall_mem measurableSet_Ioi (fun r _ => ?_)
      simp only []
      by_cases hle : r ≤ A
      · rw [Set.indicator_of_mem (Set.mem_Iic.mpr hle)]
        exact mul_nonneg (sq_nonneg r) (abs_nonneg _)
      · rw [Set.indicator_of_notMem (fun h => hle (Set.mem_Iic.mp h)), mul_zero]
        exact le_refl 0
    · -- the pointwise bound `h1`, split according to whether `r ≤ A`
      refine ae_restrict_of_forall_mem measurableSet_Ioi (fun r hr => ?_)
      simp only []
      by_cases hle : r ≤ A
      · rw [Set.indicator_of_mem (Set.mem_Iic.mpr hle),
            Set.indicator_of_mem (Set.mem_Iic.mpr hle)]
        exact mul_le_mul_of_nonneg_left (h1 r (le_of_lt hr)) (sq_nonneg r)
      · rw [Set.indicator_of_notMem (fun h => hle (Set.mem_Iic.mp h)),
            Set.indicator_of_notMem (fun h => hle (Set.mem_Iic.mp h))]
  exact mul_le_mul_of_nonneg_left hkey (by positivity)

end Work.BoseBox.LatticeModel
