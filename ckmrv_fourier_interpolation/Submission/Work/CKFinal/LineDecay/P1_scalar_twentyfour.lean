import Mathlib

namespace Work.CKFinal.LineDecay

/-- Scalar estimate behind clause (1) of the line-decay bound in dimension 24.

Writing `u = exp(-π y)`, `v = exp(-π/t)`, the denominator is `u² + v²` and the
numerator is `t¹⁰ · v · u²`; the arithmetic–geometric mean inequality
`2uv ≤ u² + v²` then gives the result, since `t¹⁰ ≤ 1`. -/
theorem P1_scalar_twentyfour :
    ∀ y t : ℝ, 1 ≤ y → 0 < t → t ≤ 1 →
      t ^ 10 * Real.exp (-(Real.pi * t⁻¹) - 2 * Real.pi * y)
        / (Real.exp (-(2 * Real.pi * y)) + Real.exp (-(2 * Real.pi * t⁻¹)))
        ≤ Real.exp (-(Real.pi * y)) := by
  intro y t hy ht0 ht1
  set u := Real.exp (-(Real.pi * y)) with hu
  set v := Real.exp (-(Real.pi * t⁻¹)) with hv
  have hu_pos : 0 < u := by rw [hu]; exact Real.exp_pos _
  have hv_pos : 0 < v := by rw [hv]; exact Real.exp_pos _
  have ht10 : t ^ 10 ≤ 1 := by
    calc t ^ 10 ≤ 1 ^ 10 := pow_le_pow_left₀ (le_of_lt ht0) ht1 10
      _ = 1 := by norm_num
  have hB : Real.exp (-(2 * Real.pi * y)) = u ^ 2 := by
    rw [hu, show -(2 * Real.pi * y) = (2:ℕ) * (-(Real.pi * y)) by ring, Real.exp_nat_mul]
  have hC : Real.exp (-(2 * Real.pi * t⁻¹)) = v ^ 2 := by
    rw [hv, show -(2 * Real.pi * t⁻¹) = (2:ℕ) * (-(Real.pi * t⁻¹)) by ring, Real.exp_nat_mul]
  have hE : Real.exp (-(Real.pi * t⁻¹) - 2 * Real.pi * y) = v * u ^ 2 := by
    rw [show -(Real.pi * t⁻¹) - 2 * Real.pi * y
          = (-(Real.pi * t⁻¹)) + (-(2 * Real.pi * y)) by ring, Real.exp_add, ← hv, hB]
  have hkey : t ^ 10 * (v * u ^ 2) ≤ u * (u ^ 2 + v ^ 2) := by
    have h1 : t ^ 10 * (v * u ^ 2) ≤ v * u ^ 2 := by
      calc t ^ 10 * (v * u ^ 2) ≤ 1 * (v * u ^ 2) :=
            mul_le_mul_of_nonneg_right ht10 (by positivity)
        _ = v * u ^ 2 := by ring
    have h2 : v * u ^ 2 ≤ u * (u ^ 2 + v ^ 2) := by
      have huv : u * v ≤ u ^ 2 + v ^ 2 := by
        nlinarith [sq_nonneg (2 * u - v), sq_nonneg u, sq_nonneg v]
      calc v * u ^ 2 = u * (u * v) := by ring
        _ ≤ u * (u ^ 2 + v ^ 2) := mul_le_mul_of_nonneg_left huv (le_of_lt hu_pos)
    linarith
  have hden : 0 < Real.exp (-(2 * Real.pi * y)) + Real.exp (-(2 * Real.pi * t⁻¹)) :=
    add_pos (Real.exp_pos _) (Real.exp_pos _)
  rw [div_le_iff₀ hden, hE, hB, hC]
  exact hkey

end Work.CKFinal.LineDecay
