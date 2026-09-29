import Mathlib

namespace Work.ResMath

/-- The two Gaussian tails beyond `ξ` and `-ξ` sum to the full Gaussian integral. -/
theorem gaussPair (a : ℝ) (ha : 0 < a) (ξ : ℝ) : (∫ x in Set.Ioi ξ, Real.exp (-a * x ^ 2)) + (∫ x in Set.Ioi (-ξ), Real.exp (-a * x ^ 2)) = Real.sqrt (Real.pi / a) := by
  have hf : MeasureTheory.Integrable (fun x : ℝ => Real.exp (-a * x ^ 2)) MeasureTheory.volume :=
    integrable_exp_neg_mul_sq ha
  -- By evenness, the integral over `Iic ξ` equals the integral over `Ioi (-ξ)`.
  have h2 : (∫ x in Set.Iic ξ, Real.exp (-a * x ^ 2)) =
      ∫ x in Set.Ioi (-ξ), Real.exp (-a * x ^ 2) := by
    have h := integral_comp_neg_Ioi (-ξ) (fun x : ℝ => Real.exp (-a * x ^ 2))
    rw [neg_neg] at h
    rw [← h]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
    ring_nf
  have h3 := MeasureTheory.integral_add_compl (s := Set.Ioi ξ) measurableSet_Ioi hf
  rw [Set.compl_Ioi] at h3
  rw [integral_gaussian a, h2] at h3
  exact h3

end Work.ResMath
