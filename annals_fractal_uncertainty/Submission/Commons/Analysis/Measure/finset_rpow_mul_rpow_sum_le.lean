import Mathlib.Analysis.MeanInequalities

namespace Commons.Analysis.Measure

open scoped Real ENNReal BigOperators

/-- Hölder's inequality for finite sums with conjugate exponents `1-κ` and `κ`:
`∑ x_i^(1-κ) y_i^κ ≤ (∑ x_i)^(1-κ) (∑ y_i)^κ` for nonnegative `x_i, y_i`. -/
theorem finset_rpow_mul_rpow_sum_le {ι : Type*} (s : Finset ι) (x y : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) :
    ∑ i ∈ s, (x i) ^ (1 - κ) * (y i) ^ κ
      ≤ (∑ i ∈ s, x i) ^ (1 - κ) * (∑ i ∈ s, y i) ^ κ := by
  rcases eq_or_lt_of_le hκ1 with h1 | hlt
  · -- Case `κ = 1`: both sides reduce to `∑ i ∈ s, y i`.
    subst h1
    simp
  · -- Case `κ < 1`: apply Hölder with conjugate exponents `(1-κ)⁻¹` and `κ⁻¹`.
    have ha : 0 < 1 - κ := by linarith
    have hb : 0 < κ := hκ0
    have hab : (1 - κ) + κ = 1 := by ring
    have hpq : (1 - κ)⁻¹.HolderConjugate κ⁻¹ := Real.HolderConjugate.inv_inv ha hb hab
    have hmain := Real.inner_le_Lp_mul_Lq_of_nonneg s
      (f := fun i => x i ^ (1 - κ)) (g := fun i => y i ^ κ) hpq
      (fun i _ => Real.rpow_nonneg (hx i) (1 - κ)) (fun i _ => Real.rpow_nonneg (hy i) κ)
    have hxa : ∀ i, (x i ^ (1 - κ)) ^ (1 - κ)⁻¹ = x i := by
      intro i
      rw [← Real.rpow_mul (hx i), mul_inv_cancel₀ (ne_of_gt ha), Real.rpow_one]
    have hyb : ∀ i, (y i ^ κ) ^ κ⁻¹ = y i := by
      intro i
      rw [← Real.rpow_mul (hy i), mul_inv_cancel₀ (ne_of_gt hb), Real.rpow_one]
    rw [Finset.sum_congr rfl (fun i _ => hxa i)] at hmain
    rw [Finset.sum_congr rfl (fun i _ => hyb i)] at hmain
    simp only [one_div, inv_inv] at hmain
    exact hmain

end Commons.Analysis.Measure