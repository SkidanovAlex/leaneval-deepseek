import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace Commons.Measure.Real

open MeasureTheory Metric Filter Set
open scoped Topology

/-- `∫_{r ∈ (a,b]} r/(1+r²) dr ≤ b/a - 1` for `0 < a ≤ b`. -/
private lemma integral_Ioc_mul_inv_one_add_sq_aux {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ r in Set.Ioc a b, r / (1 + r ^ 2)) ≤ b / a - 1 := by
  have hcont : Continuous fun r : ℝ => r / (1 + r^2) := by
    apply Continuous.div
    · exact continuous_id
    · exact continuous_const.add (continuous_id.pow 2)
    · intro r; positivity
  have hle : ∀ x ∈ Set.Icc a b, x/(1+x^2) ≤ 1/a := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le ha hx.1
    have hden : 0 < 1 + x^2 := by positivity
    rw [div_le_iff₀ hden]
    rw [one_div, inv_mul_eq_div, le_div_iff₀ ha]
    nlinarith [mul_nonneg (le_of_lt hxpos) (sub_nonneg.mpr hx.1)]
  calc (∫ r in Set.Ioc a b, r/(1+r^2))
      = ∫ r in a..b, r/(1+r^2) := (intervalIntegral.integral_of_le hab).symm
    _ ≤ ∫ r in a..b, (1/a) :=
        intervalIntegral.integral_mono_on hab (hcont.intervalIntegrable a b)
          intervalIntegrable_const hle
    _ = b/a - 1 := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
        field_simp

/-- For `0 < a ≤ b` and `A ≥ 0`, the integral over `(0,∞)` of
`A · 1_{(a,b]}(r) · r/(1+r²)` is at most `A · (b/a - 1)`. -/
theorem integral_Ioc_indicator_mul_inv_one_add_sq_le {A a b : ℝ} (hA : 0 ≤ A) (ha : 0 < a)
    (hab : a ≤ b) :
    (∫ r in Set.Ioi (0 : ℝ),
        (A * (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) r) * (r / (1 + r ^ 2)))
      ≤ A * (b / a - 1) := by
  have hsub : Set.Ioc a b ⊆ Set.Ioi (0 : ℝ) := fun r hr => lt_trans ha hr.1
  have hbound := integral_Ioc_mul_inv_one_add_sq_aux ha hab
  have hpoint : (fun r => (A * (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) r) * (r / (1 + r ^ 2)))
      = fun r => A * ((Set.Ioc a b).indicator (fun r => r / (1 + r ^ 2)) r) := by
    funext r
    by_cases hr : r ∈ Set.Ioc a b
    · rw [Set.indicator_of_mem hr, Set.indicator_of_mem hr]; ring
    · rw [Set.indicator_of_notMem hr, Set.indicator_of_notMem hr]; ring
  rw [hpoint, MeasureTheory.integral_const_mul]
  have h_inter : Set.Ioi (0 : ℝ) ∩ Set.Ioc a b = Set.Ioc a b := Set.inter_eq_right.mpr hsub
  have hInt : (∫ r in Set.Ioi (0 : ℝ), (Set.Ioc a b).indicator (fun r => r / (1 + r ^ 2)) r)
      = ∫ r in Set.Ioc a b, r / (1 + r ^ 2) := by
    rw [MeasureTheory.setIntegral_indicator measurableSet_Ioc, h_inter]
  rw [hInt]
  exact mul_le_mul_of_nonneg_left hbound hA

end Commons.Measure.Real