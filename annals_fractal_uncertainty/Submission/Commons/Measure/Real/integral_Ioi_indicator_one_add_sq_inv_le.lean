import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace Commons.Measure.Real

open MeasureTheory Metric Filter Set
open scoped Topology

/-- The integral over `(0,∞)` of `A · 1_{r>c}/(1+r²)` is at most `A/c`. -/
theorem integral_Ioi_indicator_one_add_sq_inv_le {A c : ℝ} (hA : 0 ≤ A) (hc : 0 < c) :
    (∫ r in Set.Ioi (0 : ℝ), A * (Set.Ioi c).indicator (fun _ => (1 : ℝ)) r / (1 + r ^ 2))
      ≤ A * c⁻¹ := by
  have hF : (fun r : ℝ => A * (Set.Ioi c).indicator (fun _ => (1 : ℝ)) r / (1 + r ^ 2))
      = (Set.Ioi c).indicator (fun r : ℝ => A / (1 + r ^ 2)) := by
    funext r
    by_cases h : r ∈ Set.Ioi c
    · simp [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h]
  have h_eq : (∫ r in Set.Ioi (0 : ℝ),
        A * (Set.Ioi c).indicator (fun _ => (1 : ℝ)) r / (1 + r ^ 2))
      = ∫ r in Set.Ioi c, A / (1 + r ^ 2) := by
    rw [hF, setIntegral_indicator (measurableSet_Ioi (a := c)),
      Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi (le_of_lt hc))]
  rw [h_eq]
  have h_mono : (∫ r in Set.Ioi c, (1 + r ^ 2)⁻¹) ≤ ∫ r in Set.Ioi c, (r ^ 2)⁻¹ := by
    apply setIntegral_mono_on
    · exact integrable_inv_one_add_sq.integrableOn
    · refine (integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) hc).congr_fun
        ?_ measurableSet_Ioi
      intro r hr
      have hr0 : 0 < r := lt_trans hc hr
      show r ^ (-2 : ℝ) = (r ^ 2)⁻¹
      rw [Real.rpow_neg hr0.le, Real.rpow_two]
    · exact measurableSet_Ioi
    · intro r hr
      have hr0 : 0 < r := lt_trans hc hr
      rw [inv_le_inv₀ (show (0 : ℝ) < 1 + r ^ 2 by positivity)
        (show (0 : ℝ) < r ^ 2 by exact pow_pos hr0 2)]
      nlinarith [sq_nonneg r]
  have hval : (∫ r in Set.Ioi c, (r ^ 2)⁻¹) = c⁻¹ := by
    have hcongr : (∫ r in Set.Ioi c, (r ^ 2)⁻¹) = ∫ r in Set.Ioi c, r ^ (-2 : ℝ) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      have hr0 : 0 < r := lt_trans hc hr
      show (r ^ 2)⁻¹ = r ^ (-2 : ℝ)
      rw [Real.rpow_neg hr0.le, Real.rpow_two]
    rw [hcongr, integral_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) hc]
    rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
    ring
  calc
    ∫ r in Set.Ioi c, A / (1 + r ^ 2)
        = A * ∫ r in Set.Ioi c, (1 + r ^ 2)⁻¹ := by
          simp_rw [div_eq_mul_inv]
          rw [integral_const_mul]
    _ ≤ A * ∫ r in Set.Ioi c, (r ^ 2)⁻¹ := mul_le_mul_of_nonneg_left h_mono hA
    _ = A * c⁻¹ := by rw [hval]

end Commons.Measure.Real