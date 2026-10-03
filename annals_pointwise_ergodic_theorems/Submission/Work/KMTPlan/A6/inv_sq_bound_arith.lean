import Mathlib

namespace Work.KMTPlan.A6

/-- Arithmetic bound used in the KMT bookkeeping: with `T ^ 2 = 2 * A / ε`, the two
"short" terms `8A/(R T²)` and `16A/(Q T)` are dominated by `100 · (√(Aε)/Q + ε/R)`.

Indeed `8A/(R T²) = 4ε/R` and `16A/(Q T) ≤ 12√(Aε)/Q`; both are absorbed by the RHS. -/
theorem inv_sq_bound_arith {A ε T Q R : ℝ} (hA : 0 < A) (hε : 0 < ε) (hT : 0 < T)
    (hT2 : T ^ 2 = 2 * A / ε) (hQ : 0 < Q) (hR : 0 < R) :
    8 * A / (R * T ^ 2) + 16 * A / (Q * T) ≤ 100 * (Real.sqrt (A * ε) / Q + ε / R) := by
  -- The first term collapses using `T ^ 2 = 2A/ε`.
  have hterm1 : 8 * A / (R * T ^ 2) = 4 * ε / R := by
    rw [hT2]
    field_simp
    ring
  -- The second term: `(√(Aε) · T) ^ 2 = 2A²`, whence `A ≤ √(Aε) · T`.
  have hsq : (Real.sqrt (A * ε) * T)^2 = 2 * A^2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ A * ε), hT2]
    field_simp
  have hAle : A ≤ Real.sqrt (A * ε) * T := by
    have h1 : A^2 ≤ (Real.sqrt (A * ε) * T)^2 := by
      rw [hsq]; nlinarith [sq_nonneg A]
    have h2 : |A| ≤ |Real.sqrt (A * ε) * T| := sq_le_sq.mp h1
    rwa [abs_of_nonneg hA.le, abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) hT.le)] at h2
  have h16 : 16 * A ≤ 100 * Real.sqrt (A * ε) * T := by nlinarith [hAle, hA]
  have hA1 : 8 * A / (R * T ^ 2) ≤ 100 * (ε / R) := by
    rw [hterm1]
    have : 4 * ε / R = 4 * (ε / R) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  have hA2 : 16 * A / (Q * T) ≤ 100 * (Real.sqrt (A * ε) / Q) := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < Q * T)]
    have : (100 * (Real.sqrt (A * ε) / Q)) * (Q * T) = 100 * Real.sqrt (A * ε) * T := by
      field_simp
    rw [this]
    exact h16
  calc 8 * A / (R * T ^ 2) + 16 * A / (Q * T)
      ≤ 100 * (ε / R) + 100 * (Real.sqrt (A * ε) / Q) := add_le_add hA1 hA2
    _ = 100 * (Real.sqrt (A * ε) / Q + ε / R) := by ring

end Work.KMTPlan.A6
