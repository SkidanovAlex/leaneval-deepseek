import Mathlib

namespace Work.FIArea6Road

theorem ThetaMulInvSqLeInvHeight (θ H y : ℝ) (hθ : 0 < θ) (hH : 0 < H) (hy : |y| = H) :
    θ * (1 + (θ * y) ^ 2)⁻¹ ≤ 1 / H := by
  -- `|y| = H` forces `y ^ 2 = H ^ 2`, so `(θ * y) ^ 2 = (θ * H) ^ 2`.
  have hy2 : y ^ 2 = H ^ 2 := by
    have h := sq_abs y
    rw [hy] at h
    exact h.symm
  have hApos : (0 : ℝ) < 1 + (θ * y) ^ 2 := by positivity
  -- Clear the two inverses; it suffices to show `θ * H ≤ 1 + (θ * H) ^ 2`.
  rw [← div_eq_mul_inv, div_le_iff₀ hApos, one_div, inv_mul_eq_div, le_div_iff₀ hH]
  rw [mul_pow, hy2]
  -- `1 + t ^ 2 - t = (t - 1/2) ^ 2 + 3/4 > 0` for `t = θ * H`.
  nlinarith [sq_nonneg (θ * H - 1 / 2)]

end Work.FIArea6Road
