import Mathlib

namespace Work.A3

/-- Scaling identity for the `min` that appears in the dyadic/annular decomposition of the
major-arc/β-integral: for `C > 0`, `d ≥ 1`, `N ≥ 1` and `β : ℝ`,
`min(N, C |β|^{-1/d}) = N · min(1, |((C/N)^d)⁻¹ β|^{-1/d})`, and hence the identity for the
`(2s)`-th powers.  The point is that `|((C/N)^d)⁻¹ β|^{-1/d} = (C/N) |β|^{-1/d}`, so the
`min` on the right is `min(1, (C |β|^{-1/d})/N)`, and multiplying by `N > 0` recovers the
`min` on the left. -/
theorem min_rpow_eq (C : ℝ) (hC : 0 < C) (d s N : ℕ) (hd : 1 ≤ d) (hN : 1 ≤ N) (β : ℝ) :
    (min (N : ℝ) (C * |β| ^ (-(1 : ℝ) / (d : ℝ)))) ^ (2 * s) =
      (N : ℝ) ^ (2 * s) *
        (min 1 (|(((C : ℝ) / (N : ℝ)) ^ d)⁻¹ * β| ^ (-(1 : ℝ) / (d : ℝ)))) ^ (2 * s) := by
  have hd0 : ((d : ℕ) : ℝ) ≠ 0 := by positivity
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  -- The inner factor rewrites as `((N/C)^d * β)`, whose modulus is `(N/C)^d * |β|`.
  have h_inv_d : (((C : ℝ) / (N : ℝ)) ^ d)⁻¹ = ((N : ℝ) / C) ^ d := by
    rw [← inv_pow, inv_div]
  -- The exponent arithmetic `d * (-(1/d)) = -1`.
  have hexp : ((d : ℕ) : ℝ) * (-(1 : ℝ) / (d : ℝ)) = -1 := by
    rw [neg_div, mul_neg, mul_one_div, div_self hd0]
  -- And `((N/C)^d)^{-1/d} = (N/C)^{-1} = C/N`.
  have hcore : (((N : ℝ) / C) ^ d) ^ (-(1 : ℝ) / (d : ℝ)) = C / N := by
    rw [← Real.rpow_natCast ((N : ℝ) / C) d,
      ← Real.rpow_mul (by positivity) (d : ℝ) (-(1 : ℝ) / (d : ℝ)), hexp, Real.rpow_neg_one,
      inv_div]
  -- `|((C/N)^d)⁻¹ β|^{-1/d} = (C/N) |β|^{-1/d}`.
  have h_pow : |(((C : ℝ) / (N : ℝ)) ^ d)⁻¹ * β| ^ (-(1 : ℝ) / (d : ℝ))
      = (C / N) * |β| ^ (-(1 : ℝ) / (d : ℝ)) := by
    rw [h_inv_d, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < ((N : ℝ) / C) ^ d)]
    rw [Real.mul_rpow (by positivity) (abs_nonneg β), hcore]
  -- `C |β|^{-1/d} = N * ((C/N) |β|^{-1/d})`.
  have hNC : (N : ℝ) * (C / (N : ℝ)) = C := by
    have hN0 : (N : ℝ) ≠ 0 := by positivity
    field_simp
  have hf : (N : ℝ) * ((C / N) * |β| ^ (-(1 : ℝ) / (d : ℝ)))
      = C * |β| ^ (-(1 : ℝ) / (d : ℝ)) := by
    rw [← mul_assoc, hNC]
  -- Hence the two `min`s match up to the factor `N > 0`.
  have hmin : min (N : ℝ) (C * |β| ^ (-(1 : ℝ) / (d : ℝ)))
      = (N : ℝ) * min 1 (|(((C : ℝ) / (N : ℝ)) ^ d)⁻¹ * β| ^ (-(1 : ℝ) / (d : ℝ))) := by
    rw [h_pow]
    rw [mul_min_of_nonneg (1 : ℝ) ((C : ℝ) / (N : ℝ) * |β| ^ (-(1 : ℝ) / (d : ℝ)))
      (le_of_lt hNpos), mul_one, hf]
  rw [hmin, mul_pow]

end Work.A3
