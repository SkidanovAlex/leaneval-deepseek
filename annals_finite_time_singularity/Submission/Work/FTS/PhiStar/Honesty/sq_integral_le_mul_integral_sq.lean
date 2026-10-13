import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.PhiStar.Honesty

/-- Cauchy–Schwarz on an interval: for `0 ≤ z` and `f`, `f²` interval integrable on `0..z`,
the square of the integral of `f` is at most `z` times the integral of `f²`.
Proved by integrating the nonnegative quadratic `(f - c)²`. -/
theorem sq_integral_le_mul_integral_sq {f : ℝ → ℝ} {z : ℝ} (hz : 0 ≤ z)
    (hf : IntervalIntegrable f volume 0 z)
    (hf2 : IntervalIntegrable (fun t : ℝ => f t ^ 2) volume 0 z) :
    (∫ t in (0 : ℝ)..z, f t) ^ 2 ≤ z * ∫ t in (0 : ℝ)..z, f t ^ 2 := by
  rcases eq_or_lt_of_le hz with hz0 | hzpos
  · subst hz0
    simp [intervalIntegral.integral_same]
  · set A : ℝ := ∫ t in (0 : ℝ)..z, f t with hA
    set B : ℝ := ∫ t in (0 : ℝ)..z, f t ^ 2 with hB
    have key : ∀ c : ℝ, 0 ≤ c ^ 2 * z - 2 * c * A + B := by
      intro c
      have hA1 : IntervalIntegrable (fun t : ℝ => f t ^ 2 - 2 * c * f t) volume 0 z :=
        hf2.sub (hf.const_mul (2 * c))
      have hA2 : IntervalIntegrable (fun _ : ℝ => c ^ 2) volume 0 z :=
        intervalIntegrable_const
      have hiden : (∫ t in (0 : ℝ)..z, (f t - c) ^ 2) = c ^ 2 * z - 2 * c * A + B := by
        have h1 : (∫ t in (0 : ℝ)..z, (f t - c) ^ 2)
            = ∫ t in (0 : ℝ)..z, (f t ^ 2 - 2 * c * f t + c ^ 2) := by
          apply intervalIntegral.integral_congr
          intro t _
          ring
        rw [h1, intervalIntegral.integral_add hA1 hA2,
          intervalIntegral.integral_sub hf2 (hf.const_mul (2 * c)),
          intervalIntegral.integral_const_mul (2 * c) f,
          intervalIntegral.integral_const]
        rw [← hA, ← hB]
        simp only [smul_eq_mul, sub_zero]
        ring
      have hnn : 0 ≤ ∫ t in (0 : ℝ)..z, (f t - c) ^ 2 :=
        intervalIntegral.integral_nonneg hz (fun u _ => sq_nonneg (f u - c))
      rw [hiden] at hnn
      exact hnn
    have hzA := key (A / z)
    have hexp : z * ((A / z) ^ 2 * z - 2 * (A / z) * A + B) = B * z - A ^ 2 := by
      field_simp [ne_of_gt hzpos]
      ring
    have hle : A ^ 2 ≤ B * z := by
      have h : 0 ≤ B * z - A ^ 2 := by
        rw [← hexp]
        exact mul_nonneg hzpos.le hzA
      linarith
    rw [mul_comm z B]
    exact hle

end Work.FTS.PhiStar.Honesty
