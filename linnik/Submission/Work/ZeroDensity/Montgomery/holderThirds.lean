import Mathlib

namespace Work.ZeroDensity.Montgomery

/-- **Hölder's inequality for finite sums with exponents `3` and `3/2`.** For nonnegative `x i`,
`y i` on a finite set `s` one has
`∑_{i ∈ s} x i ^ (1/3) * y i ^ (2/3) ≤ (∑_{i ∈ s} x i) ^ (1/3) * (∑_{i ∈ s} y i) ^ (2/3)`,
where the powers are real powers. -/
theorem holderThirds {ι : Type*} (s : Finset ι) (x y : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) (hy : ∀ i ∈ s, 0 ≤ y i) :
    ∑ i ∈ s, x i ^ ((1 : ℝ) / 3) * y i ^ ((2 : ℝ) / 3)
      ≤ (∑ i ∈ s, x i) ^ ((1 : ℝ) / 3) * (∑ i ∈ s, y i) ^ ((2 : ℝ) / 3) := by
  -- Hölder's inequality with conjugate exponents `p = 3`, `q = 3/2`.
  have hpq : (3 : ℝ).HolderConjugate (3 / 2) := by
    have := Real.holderConjugate_one_div (show (0 : ℝ) < 1 / 3 by norm_num)
      (show (0 : ℝ) < 2 / 3 by norm_num) (show (1 : ℝ) / 3 + 2 / 3 = 1 by norm_num)
    simpa using this
  have hf : ∀ i ∈ s, 0 ≤ x i ^ ((1 : ℝ) / 3) := fun i hi => Real.rpow_nonneg (hx i hi) _
  have hg : ∀ i ∈ s, 0 ≤ y i ^ ((2 : ℝ) / 3) := fun i hi => Real.rpow_nonneg (hy i hi) _
  have key := Real.inner_le_Lp_mul_Lq_of_nonneg (s := s) (f := fun i => x i ^ ((1 : ℝ) / 3))
    (g := fun i => y i ^ ((2 : ℝ) / 3)) (p := 3) (q := 3 / 2) hpq hf hg
  -- `(x i ^ (1/3)) ^ 3 = x i` and `(y i ^ (2/3)) ^ (3/2) = y i`, plus `1 / (3/2) = 2/3`.
  have hx3 : ∀ i ∈ s, (x i ^ ((1 : ℝ) / 3)) ^ (3 : ℝ) = x i := fun i hi => by
    rw [← Real.rpow_mul (hx i hi), show ((1 : ℝ) / 3 * 3) = 1 by norm_num, Real.rpow_one]
  have hy3 : ∀ i ∈ s, (y i ^ ((2 : ℝ) / 3)) ^ ((3 : ℝ) / 2) = y i := fun i hi => by
    rw [← Real.rpow_mul (hy i hi), show ((2 : ℝ) / 3 * (3 / 2)) = 1 by norm_num, Real.rpow_one]
  rw [Finset.sum_congr rfl hx3, Finset.sum_congr rfl hy3,
    show ((1 : ℝ) / (3 / 2)) = 2 / 3 by norm_num] at key
  exact key

end Work.ZeroDensity.Montgomery
