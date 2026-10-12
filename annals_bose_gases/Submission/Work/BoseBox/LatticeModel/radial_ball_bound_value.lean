import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.BoseBox.LatticeModel.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory Set

namespace Work.BoseBox.LatticeModel

/-- The value of the radial ball integral of the model bracket.  On `r > 0` the
integrand `r² · 1_{r ≤ A} (c + c²/(2r²))` equals `1_{0 < r ≤ A} (c r² + c²/2)`, and
`∫_{0..A} (c r² + c²/2) = c A³/3 + c² A/2`. -/
lemma radial_ball_bound_value {c A : ℝ} (hA : 0 ≤ A) :
    (∫ r in Set.Ioi (0 : ℝ), r ^ 2 * (Set.Iic A).indicator (fun s : ℝ => c + c ^ 2 / (2 * s ^ 2)) r)
      = c * A ^ 3 / 3 + c ^ 2 * A / 2 := by
  -- Reduction to a polynomial integral over `(0, A]`.
  have hpt : Set.EqOn
      (fun r : ℝ => r ^ 2 * (Set.Iic A).indicator (fun s : ℝ => c + c ^ 2 / (2 * s ^ 2)) r)
      ((Set.Ioc (0 : ℝ) A).indicator (fun r : ℝ => c * r ^ 2 + c ^ 2 / 2))
      (Set.Ioi (0 : ℝ)) := by
    intro r hr
    show r ^ 2 * (Set.Iic A).indicator (fun s : ℝ => c + c ^ 2 / (2 * s ^ 2)) r
      = (Set.Ioc (0 : ℝ) A).indicator (fun r : ℝ => c * r ^ 2 + c ^ 2 / 2) r
    by_cases hle : r ≤ A
    · rw [Set.indicator_of_mem (Set.mem_Iic.mpr hle),
          Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hr, hle⟩)]
      have hr0 : r ≠ 0 := ne_of_gt hr
      field_simp
    · rw [Set.indicator_of_notMem (fun h => hle (Set.mem_Iic.mp h)),
          Set.indicator_of_notMem (fun h => hle h.2), mul_zero]
  rw [setIntegral_congr_fun measurableSet_Ioi hpt,
      setIntegral_indicator measurableSet_Ioc,
      Set.inter_eq_right.mpr (fun x hx => hx.1),
      ← intervalIntegral.integral_of_le hA]
  -- Evaluation of `∫₀^A (c r² + c²/2)`.
  have h1 : IntervalIntegrable (fun x : ℝ => c * x ^ 2) volume 0 A :=
    (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable 0 A
  have h2 : IntervalIntegrable (fun _ : ℝ => c ^ 2 / 2) volume 0 A :=
    continuous_const.intervalIntegrable 0 A
  rw [intervalIntegral.integral_add h1 h2, intervalIntegral.integral_const_mul, integral_pow,
      intervalIntegral.integral_const]
  simp
  ring

end Work.BoseBox.LatticeModel
