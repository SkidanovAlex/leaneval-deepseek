import Mathlib

namespace Work.HP.BallConeK

open MeasureTheory intervalIntegral

/-- The derivative of `t ↦ -1 / t ^ k` is `t ↦ k / t ^ (k + 1)` away from `0`. -/
lemma hasDerivAt_neg_one_div_pow (k : ℕ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun t : ℝ => -1 / t ^ k) ((k : ℝ) / x ^ (k + 1)) x := by
  have h := (hasDerivAt_zpow (-(k : ℤ)) x (Or.inl hx)).neg
  convert h using 1
  · ext t
    change -1 / t ^ k = -(t ^ (-(k : ℤ)))
    rw [div_eq_mul_inv, zpow_neg, zpow_natCast]
    ring
  · rw [show ((-(k : ℤ) : ℤ) : ℝ) = -(k : ℝ) by push_cast; ring]
    rw [neg_mul, neg_neg]
    rw [show (-(k : ℤ) - 1 : ℤ) = -(((k + 1 : ℕ)) : ℤ) by omega, zpow_neg, zpow_natCast]
    rw [div_eq_mul_inv]

theorem integralDivPow (k : ℕ) {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) :
    ∫ t in A..B, (k : ℝ) / t ^ (k + 1) = 1 / A ^ k - 1 / B ^ k := by
  have hderiv : ∀ x ∈ Set.uIcc A B,
      HasDerivAt (fun t : ℝ => -1 / t ^ k) ((k : ℝ) / x ^ (k + 1)) x := by
    intro x hx
    rw [Set.uIcc_of_le hAB] at hx
    have hx0 : x ≠ 0 := by
      have : A ≤ x := hx.1
      linarith
    exact hasDerivAt_neg_one_div_pow k hx0
  have hcont : ContinuousOn (fun t : ℝ => (k : ℝ) / t ^ (k + 1)) (Set.uIcc A B) := by
    apply ContinuousOn.div continuousOn_const
    · exact continuousOn_id.pow (k + 1)
    · intro t ht
      rw [Set.uIcc_of_le hAB] at ht
      exact pow_ne_zero _ (by have : A ≤ t := ht.1; linarith : t ≠ 0)
  have hint : IntervalIntegrable (fun t : ℝ => (k : ℝ) / t ^ (k + 1)) volume A B :=
    hcont.intervalIntegrable
  have hsub := integral_eq_sub_of_hasDerivAt hderiv hint
  rw [hsub]
  ring

end Work.HP.BallConeK
