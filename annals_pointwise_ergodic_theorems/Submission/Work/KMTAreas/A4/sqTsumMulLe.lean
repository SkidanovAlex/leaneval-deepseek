import Mathlib

namespace Work.KMTAreas.A4

/-- Cauchy–Schwarz for `ℓ²(ℤ)`, in the form of the squared inequality: for nonnegative `a, c`
with summable squares, `(∑ a y * c y)^2 ≤ (∑ a y^2) * (∑ c y^2)`. -/
theorem sqTsumMulLe (a c : ℤ → ℝ) (ha0 : ∀ y : ℤ, 0 ≤ a y) (hc0 : ∀ y : ℤ, 0 ≤ c y) (ha2 : Summable fun y : ℤ => a y ^ 2) (hc2 : Summable fun y : ℤ => c y ^ 2) : (∑' y : ℤ, a y * c y) ^ 2 ≤ (∑' y : ℤ, a y ^ 2) * (∑' y : ℤ, c y ^ 2) := by
  -- Hölder's inequality at the conjugate exponents `p = q = 2`.
  obtain ⟨hsum, hcs⟩ := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg
    (p := 2) (q := 2) Real.HolderConjugate.two_two ha0 hc0
    (by simpa [Real.rpow_two] using ha2) (by simpa [Real.rpow_two] using hc2)
  have hS : 0 ≤ ∑' y : ℤ, a y * c y := tsum_nonneg fun y => mul_nonneg (ha0 y) (hc0 y)
  have hP : 0 ≤ ∑' y : ℤ, a y ^ 2 := tsum_nonneg fun y => pow_nonneg (ha0 y) 2
  have hQ : 0 ≤ ∑' y : ℤ, c y ^ 2 := tsum_nonneg fun y => pow_nonneg (hc0 y) 2
  have hXY : ∑' y : ℤ, a y * c y ≤
      (∑' y : ℤ, a y ^ 2) ^ (1 / 2 : ℝ) * (∑' y : ℤ, c y ^ 2) ^ (1 / 2 : ℝ) := by
    simpa [Real.rpow_two] using hcs
  calc (∑' y : ℤ, a y * c y) ^ 2
      ≤ ((∑' y : ℤ, a y ^ 2) ^ (1 / 2 : ℝ) * (∑' y : ℤ, c y ^ 2) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ hS hXY 2
    _ = (∑' y : ℤ, a y ^ 2) * (∑' y : ℤ, c y ^ 2) := by
        rw [mul_pow, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sq_sqrt hP, Real.sq_sqrt hQ]

end Work.KMTAreas.A4
