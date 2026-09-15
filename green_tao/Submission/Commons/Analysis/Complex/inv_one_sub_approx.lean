import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes

namespace Commons.Analysis.Complex

/-- Elementary bounds for `(1 - a)⁻¹` when `‖a‖ ≤ 1/2` (complex numbers).
Proof sketch: `1 - a` is invertible since `‖a‖ < 1`; from `(1 - a)⁻¹ = 1 + a * (1 - a)⁻¹` we get
`‖(1-a)⁻¹‖ ≤ 1 + ‖a‖‖(1-a)⁻¹‖`, hence `‖(1-a)⁻¹‖ ≤ 1/(1 - ‖a‖) ≤ 2`; then
`(1-a)⁻¹ - (1+a) = a^2 * (1-a)⁻¹`, so `‖(1-a)⁻¹ - (1+a)‖ ≤ ‖a‖^2 * 2 ≤ 4 * ‖a‖^2`. -/
theorem inv_one_sub_approx {a : ℂ} (ha : ‖a‖ ≤ 1 / 2) :
    ‖(1 - a)⁻¹‖ ≤ 2 ∧ ‖(1 - a)⁻¹ - (1 + a)‖ ≤ 4 * ‖a‖ ^ 2 := by
  have hne : (1 : ℂ) - a ≠ 0 := by
    intro h
    have ha1 : a = 1 := by
      rw [sub_eq_zero] at h
      exact h.symm
    rw [ha1, norm_one] at ha
    norm_num at ha
  have hlb : (1 : ℝ) / 2 ≤ ‖(1 : ℂ) - a‖ := by
    have h := norm_sub_norm_le (1 : ℂ) a
    rw [norm_one] at h
    linarith
  have hpart1 : ‖(1 - a)⁻¹‖ ≤ 2 := by
    rw [norm_inv]
    calc ‖(1 : ℂ) - a‖⁻¹ ≤ ((1 : ℝ) / 2)⁻¹ := inv_anti₀ (by norm_num) hlb
      _ = 2 := by norm_num
  refine ⟨hpart1, ?_⟩
  have hone : (1 + a + a ^ 2 * (1 - a)⁻¹) = (1 - a)⁻¹ := by
    have h : (1 - a) * (1 + a + a ^ 2 * (1 - a)⁻¹) = 1 := by
      have h1 : (1 - a) * (1 + a) = 1 - a ^ 2 := by ring
      have h2 : (1 - a) * (a ^ 2 * (1 - a)⁻¹) = a ^ 2 := by
        rw [mul_comm (1 - a) (a ^ 2 * (1 - a)⁻¹), mul_assoc, inv_mul_cancel₀ hne, mul_one]
      rw [mul_add, h1, h2]
      ring
    calc (1 + a + a ^ 2 * (1 - a)⁻¹)
        = ((1 - a)⁻¹ * (1 - a)) * (1 + a + a ^ 2 * (1 - a)⁻¹) := by
          rw [inv_mul_cancel₀ hne, one_mul]
      _ = (1 - a)⁻¹ * ((1 - a) * (1 + a + a ^ 2 * (1 - a)⁻¹)) := by ring
      _ = (1 - a)⁻¹ * 1 := by rw [h]
      _ = (1 - a)⁻¹ := by ring
  have hident : (1 - a)⁻¹ - (1 + a) = a ^ 2 * (1 - a)⁻¹ := by
    conv_lhs => rw [← hone]
    rw [add_sub_cancel_left]
  rw [hident, norm_mul, norm_pow]
  nlinarith [hpart1, sq_nonneg ‖a‖]

end Commons.Analysis.Complex