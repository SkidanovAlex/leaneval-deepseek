import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr

open MeasureTheory

/-- **Cauchy–Schwarz on an interval.** For `a ≤ b` and `f²` interval integrable on `a..b`,
the square of the integral of `f` is at most `(b - a)` times the integral of `f²`:
`(∫_a^b f)² ≤ (b - a) ∫_a^b f²`.

The proof splits on whether `f` is itself interval integrable. If it is not, the interval
integral of `f` is `0` (`intervalIntegral.integral_undef`) and the right-hand side is
nonnegative. If it is, integrate the nonnegative quadratic `(f - c)²` for the optimal
`c = (∫ f)/(b - a)`. -/
theorem sq_integral_interval_le {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hi : IntervalIntegrable (fun x : ℝ => (f x) ^ 2) MeasureTheory.volume a b) :
    (∫ x in a..b, f x) ^ 2 ≤ (b - a) * ∫ x in a..b, (f x) ^ 2 := by
  rcases eq_or_lt_of_le hab with hab' | hab'
  · -- degenerate interval
    rw [hab']
    simp [intervalIntegral.integral_same]
  · by_cases hf : IntervalIntegrable f volume a b
    · -- the integral of `f` is a genuine number: integrate the nonnegative quadratic `(f - c)²`
      set A : ℝ := ∫ t in a..b, f t with hA
      set B : ℝ := ∫ t in a..b, f t ^ 2 with hB
      have key : ∀ c : ℝ, 0 ≤ c ^ 2 * (b - a) - 2 * c * A + B := by
        intro c
        have hA1 : IntervalIntegrable (fun t : ℝ => f t ^ 2 - 2 * c * f t) volume a b :=
          hi.sub (hf.const_mul (2 * c))
        have hA2 : IntervalIntegrable (fun _ : ℝ => c ^ 2) volume a b :=
          intervalIntegrable_const
        have hiden : (∫ t in a..b, (f t - c) ^ 2) = c ^ 2 * (b - a) - 2 * c * A + B := by
          have h1 : (∫ t in a..b, (f t - c) ^ 2)
              = ∫ t in a..b, (f t ^ 2 - 2 * c * f t + c ^ 2) := by
            apply intervalIntegral.integral_congr
            intro t _
            ring
          rw [h1, intervalIntegral.integral_add hA1 hA2,
            intervalIntegral.integral_sub hi (hf.const_mul (2 * c)),
            intervalIntegral.integral_const_mul (2 * c) f,
            intervalIntegral.integral_const]
          rw [← hA, ← hB]
          simp only [smul_eq_mul]
          ring
        have hnn : 0 ≤ ∫ t in a..b, (f t - c) ^ 2 :=
          intervalIntegral.integral_nonneg hab (fun u _ => sq_nonneg (f u - c))
        rw [hiden] at hnn
        exact hnn
      have hd : 0 < b - a := sub_pos.mpr hab'
      have hkey := key (A / (b - a))
      have hexp : (b - a) * ((A / (b - a)) ^ 2 * (b - a) - 2 * (A / (b - a)) * A + B)
          = B * (b - a) - A ^ 2 := by
        field_simp [ne_of_gt hd]
        ring
      have hle : A ^ 2 ≤ B * (b - a) := by
        have h : 0 ≤ B * (b - a) - A ^ 2 := by
          rw [← hexp]
          exact mul_nonneg hd.le hkey
        linarith
      rw [mul_comm (b - a) B]
      exact hle
    · -- `f` is not interval integrable: its interval integral vanishes and the right side is ≥ 0
      rw [intervalIntegral.integral_undef hf]
      have h2 : 0 ≤ (b - a) * ∫ x in a..b, f x ^ 2 :=
        mul_nonneg (sub_nonneg.mpr hab)
          (intervalIntegral.integral_nonneg hab (fun u _ => sq_nonneg (f u)))
      have h0 : (0 : ℝ) ^ 2 = 0 := by norm_num
      rw [h0]
      exact h2

end Work.FTS.StrongEps.EpsE4Thr
