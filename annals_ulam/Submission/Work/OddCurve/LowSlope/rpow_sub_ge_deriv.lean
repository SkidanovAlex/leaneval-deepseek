import Mathlib

namespace Work.OddCurve.LowSlope

/-- For `0 < θ ≤ 1` and `0 < x ≤ y`, the secant slope of `t ↦ t ^ θ` on `[x, y]` is at least
the derivative of `t ↦ t ^ θ` at the right endpoint `y`; equivalently `t ↦ t^θ` lies below its
tangent line at `y`. This is the standard concavity estimate for the power function with
exponent in `(0, 1]`. -/
theorem rpow_sub_ge_deriv {θ x y : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hx : 0 < x) (hxy : x ≤ y) :
    θ * y ^ (θ - 1) * (y - x) ≤ y ^ θ - x ^ θ := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hyne : y ≠ 0 := hy.ne'
  have hyθpos : 0 < y ^ θ := Real.rpow_pos_of_pos hy θ
  -- Bernoulli's inequality at `s = (x - y)/y`, which satisfies `s ≥ -1` since `x ≥ 0`.
  have hs : -1 ≤ (x - y) / y := by
    rw [le_div_iff₀ hy]
    nlinarith
  have hber : (1 + (x - y) / y) ^ θ ≤ 1 + θ * ((x - y) / y) :=
    rpow_one_add_le_one_add_mul_self hs hθ0.le hθ1
  have h1s : (1 + (x - y) / y) = x / y := by
    field_simp
    ring
  rw [h1s] at hber
  -- multiply by `y ^ θ > 0`
  have hmul := mul_le_mul_of_nonneg_right hber hyθpos.le
  have hl : (x / y) ^ θ * y ^ θ = x ^ θ := by
    rw [Real.div_rpow hx.le hy.le θ, div_mul_cancel₀ _ hyθpos.ne']
  have hr : (1 + θ * ((x - y) / y)) * y ^ θ = y ^ θ - θ * y ^ (θ - 1) * (y - x) := by
    have hkey : θ * ((x - y) / y) * y ^ θ = θ * ((x - y) * y ^ (θ - 1)) := by
      rw [mul_assoc, div_mul_eq_mul_div, mul_div_assoc, ← Real.rpow_sub_one hyne θ]
    rw [add_mul, one_mul, hkey]
    ring
  rw [hl, hr] at hmul
  linarith

end Work.OddCurve.LowSlope
