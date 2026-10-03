import Mathlib

namespace Work.Parab.coverCone

/-- If `|arg z| ≤ 7π/12` then the angle of `-1/z` lies in the cone where its real part is
at most one third of its modulus: `(-1/z).re ≤ ‖-1/z‖/3`.  The constant comes from
`cos (7π/12) = -sin (π/12) ≥ -1/3`. -/
theorem inv_neg_norm_re {z : ℂ} (hz : z ≠ 0) (harg : |z.arg| ≤ 7 * Real.pi / 12) :
    ‖-1 / z‖ = 1 / ‖z‖ ∧ (-1 / z).re ≤ ‖-1 / z‖ / 3 := by
  have hnorm : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hnormne : ‖z‖ ≠ 0 := ne_of_gt hnorm
  have hnorm_eq : ‖-1 / z‖ = 1 / ‖z‖ := by
    rw [norm_div, norm_neg, norm_one]
  refine ⟨hnorm_eq, ?_⟩
  -- cos (5π/12) = sin (π/12) ≤ π/12 < 1/3, hence cos (7π/12) = -cos (5π/12) ≥ -1/3
  have hc5 : Real.cos (5 * Real.pi / 12) = Real.sin (Real.pi / 12) := by
    rw [← Real.sin_pi_div_two_sub (5 * Real.pi / 12),
      show Real.pi / 2 - 5 * Real.pi / 12 = Real.pi / 12 by ring]
  have hcos5le : Real.cos (5 * Real.pi / 12) ≤ 1 / 3 := by
    rw [hc5]
    have h1 : Real.sin (Real.pi / 12) ≤ Real.pi / 12 := Real.sin_le (by positivity)
    have h2 : Real.pi / 12 < 1 / 3 := by linarith [Real.pi_lt_four, Real.pi_pos]
    linarith
  have hcos7 : -(1 / 3 : ℝ) ≤ Real.cos (7 * Real.pi / 12) := by
    rw [show 7 * Real.pi / 12 = Real.pi - 5 * Real.pi / 12 by ring, Real.cos_pi_sub]
    linarith
  -- cosine is decreasing on [0, π] and even, so cos θ ≥ cos (7π/12) for |θ| ≤ 7π/12
  have hcos : -(1 / 3 : ℝ) ≤ Real.cos z.arg := by
    rcases le_or_gt 0 z.arg with h0 | h0
    · have h := Real.cos_le_cos_of_nonneg_of_le_pi h0 (by linarith [Real.pi_pos]) (abs_le.mp harg).2
      linarith
    · have hle : -z.arg ≤ 7 * Real.pi / 12 := by
        have := (abs_le.mp harg).1; linarith
      have h0' : 0 ≤ -z.arg := by linarith
      have h := Real.cos_le_cos_of_nonneg_of_le_pi h0' (by linarith [Real.pi_pos]) hle
      rw [Real.cos_neg] at h
      linarith
  -- explicit value of the real part
  have hzre : z.re = ‖z‖ * Real.cos z.arg := (Complex.norm_mul_cos_arg z).symm
  have hre : (-1 / z).re = -Real.cos z.arg / ‖z‖ := by
    have h1 : (-1 / z : ℂ) = -(z⁻¹) := by rw [div_eq_mul_inv]; ring
    rw [h1, Complex.neg_re, Complex.inv_re, hzre, Complex.normSq_eq_norm_sq]
    field_simp
  rw [hre, hnorm_eq]
  rw [show (1 / ‖z‖) / 3 = (1 / 3 : ℝ) / ‖z‖ by ring]
  exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hnorm)

end Work.Parab.coverCone
