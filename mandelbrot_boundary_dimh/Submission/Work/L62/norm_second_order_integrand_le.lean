import Mathlib

namespace Work.L62

/-- **Pointwise bound on the second-order Cauchy kernel.**

If `‖f‖ ≤ M` on the circle `sphere c R`, `0 < R`, `0 ≤ M` and `‖u - c‖ ≤ R/2`, then for every
`z` on the circle `|z - c| = R` (so in particular `z ≠ c` and `z ≠ u`) the integrand
`f z · (u-c)^2/((z-u)(z-c)^2)` of the Cauchy representation of the second-order remainder is
bounded by `M ‖u-c‖² / ((R/2) R²)`; this uses `|z - u| ≥ R - ‖u-c‖ ≥ R/2` and `|z - c| = R`. -/
theorem norm_second_order_integrand_le {f : ℂ → ℂ} {c u : ℂ} {R M : ℝ} (hR : 0 < R)
    (hM0 : 0 ≤ M) (hM : ∀ z ∈ Metric.sphere c R, ‖f z‖ ≤ M) (hu : ‖u - c‖ ≤ R / 2) :
    ∀ z ∈ Metric.sphere c R,
      ‖(((u - c) ^ 2 / ((z - u) * (z - c) ^ 2) : ℂ) • f z)‖
        ≤ M * ‖u - c‖ ^ 2 / ((R / 2) * R ^ 2) := by
  intro z hz
  -- `z` lies on the circle `|z - c| = R`
  have hzc : ‖z - c‖ = R := by
    rw [Metric.mem_sphere, dist_eq_norm] at hz
    exact hz
  -- reverse triangle inequality: `R = |z - c| ≤ |z - u| + |u - c|`
  have hzu : R / 2 ≤ ‖z - u‖ := by
    have h1 : ‖z - c‖ ≤ ‖z - u‖ + ‖u - c‖ := by
      calc ‖z - c‖ = ‖(z - u) + (u - c)‖ := by ring_nf
        _ ≤ ‖z - u‖ + ‖u - c‖ := norm_add_le _ _
    rw [hzc] at h1
    linarith
  have hDpos : 0 < (R / 2) * R ^ 2 := by positivity
  -- the norm of the scalar kernel
  have hnorm : ‖(((u - c) ^ 2 / ((z - u) * (z - c) ^ 2) : ℂ))‖
      = ‖u - c‖ ^ 2 / (‖z - u‖ * R ^ 2) := by
    rw [norm_div, norm_mul, norm_pow, norm_pow, hzc]
  -- denominator comparison
  have hle1 : ‖u - c‖ ^ 2 / (‖z - u‖ * R ^ 2) ≤ ‖u - c‖ ^ 2 / ((R / 2) * R ^ 2) := by
    apply div_le_div_of_nonneg_left (sq_nonneg _) hDpos
    exact mul_le_mul_of_nonneg_right hzu (sq_nonneg R)
  calc ‖(((u - c) ^ 2 / ((z - u) * (z - c) ^ 2) : ℂ) • f z)‖
      = ‖(((u - c) ^ 2 / ((z - u) * (z - c) ^ 2) : ℂ))‖ * ‖f z‖ := norm_smul _ _
    _ = ‖u - c‖ ^ 2 / (‖z - u‖ * R ^ 2) * ‖f z‖ := by rw [hnorm]
    _ ≤ ‖u - c‖ ^ 2 / ((R / 2) * R ^ 2) * ‖f z‖ := mul_le_mul_of_nonneg_right hle1 (norm_nonneg _)
    _ ≤ ‖u - c‖ ^ 2 / ((R / 2) * R ^ 2) * M :=
        mul_le_mul_of_nonneg_left (hM z hz) (div_nonneg (sq_nonneg _) hDpos.le)
    _ = M * ‖u - c‖ ^ 2 / ((R / 2) * R ^ 2) := by ring

end Work.L62
