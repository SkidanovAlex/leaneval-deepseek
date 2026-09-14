import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.Analysis.Asymptotic

lemma sqrt_le_sqrt_mul_rpow_neg_third {A C t : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (ht : 0 < t)
    (h : A ≤ C * t ^ (-(2:ℝ)/3)) : Real.sqrt A ≤ Real.sqrt C * t ^ (-(1:ℝ)/3) := by
  have ht0 : 0 ≤ t := le_of_lt ht
  have h2 : Real.sqrt A ≤ Real.sqrt (C * t ^ (-(2:ℝ)/3)) := Real.sqrt_le_sqrt h
  have hmul : Real.sqrt (C * t ^ (-(2:ℝ)/3)) = Real.sqrt C * Real.sqrt (t ^ (-(2:ℝ)/3)) :=
    Real.sqrt_mul hC _
  have hsqrt : Real.sqrt (t ^ (-(2:ℝ)/3)) = t ^ (-(1:ℝ)/3) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht0]
    norm_num
  rw [hmul, hsqrt] at h2
  exact h2

end Commons.Analysis.Asymptotic