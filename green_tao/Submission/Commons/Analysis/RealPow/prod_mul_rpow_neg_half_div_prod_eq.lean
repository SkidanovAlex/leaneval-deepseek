import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.Analysis.RealPow

theorem prod_mul_rpow_neg_half_div_prod_eq (B : ℝ) (t : Finset ℕ) (hpos : ∀ p ∈ t, 0 < p) :
    (∏ p ∈ t, B * (p:ℝ)^(-(1/2:ℝ))) * (∏ p ∈ t, (p:ℝ))⁻¹
      = ∏ p ∈ t, B * (p:ℝ)^(-(3/2:ℝ)) := by
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hpos p hp
  rw [mul_assoc, ← Real.rpow_neg_one, ← Real.rpow_add hp0]
  have hExp : (-(1/2:ℝ)) + (-1) = -(3/2:ℝ) := by norm_num
  rw [hExp]

end Commons.Analysis.RealPow