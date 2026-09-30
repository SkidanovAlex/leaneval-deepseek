import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Pointwise estimate on a circle for a residue integrand (BW §19 (27)): if `|z − l| = η ≤ 1`,
`κ ≤ |s − l|`, `η < κ`, `F s ≠ 0` and `‖F s‖ ≤ ‖F z‖ e^Y`, then
`‖(z−l)^m / ((z−s) F z)‖ ≤ e^Y / ((κ−η)‖F s‖)`. -/
lemma jsum_integrand_bound (F : ℂ → ℂ) (Y η κ : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) (hκη : η < κ)
    (s z l : ℂ) (m : ℕ) (hz : ‖z - l‖ = η) (hsl : κ ≤ ‖s - l‖) (hFs : F s ≠ 0)
    (hY : ‖F s‖ ≤ ‖F z‖ * Real.exp Y) :
    ‖(z - l) ^ m / ((z - s) * F z)‖ ≤ Real.exp Y / ((κ - η) * ‖F s‖) := by
  have hκpos : 0 < κ - η := sub_pos.mpr hκη
  have hFspos : 0 < ‖F s‖ := norm_pos_iff.mpr hFs
  -- `F z ≠ 0` because otherwise `‖F s‖ ≤ 0`.
  have hFz_ne : F z ≠ 0 := by
    intro h
    rw [h, norm_zero, zero_mul] at hY
    exact absurd hY (not_le.mpr hFspos)
  have hFzpos : 0 < ‖F z‖ := norm_pos_iff.mpr hFz_ne
  -- Distance estimate: `‖s - l‖ ≤ ‖s - z‖ + ‖z - l‖`, hence `κ - η ≤ ‖z - s‖`.
  have hzs : κ - η ≤ ‖z - s‖ := by
    have h1 : ‖s - l‖ ≤ ‖z - s‖ + η := by
      have h := norm_add_le (s - z) (z - l)
      rw [show (s - z) + (z - l) = s - l by ring] at h
      rw [hz, norm_sub_rev s z] at h
      exact h
    linarith
  have hA : 0 < ‖z - s‖ * ‖F z‖ := mul_pos (lt_of_lt_of_le hκpos hzs) hFzpos
  have hB : 0 < (κ - η) * ‖F s‖ := mul_pos hκpos hFspos
  have hηm : η ^ m ≤ 1 := pow_le_one₀ hη.le hη1
  -- Compute the norm of the integrand.
  have hN : ‖(z - l) ^ m / ((z - s) * F z)‖ = η ^ m / (‖z - s‖ * ‖F z‖) := by
    rw [norm_div, norm_mul, norm_pow, hz]
  rw [hN]
  -- Cross-multiplied form of the target inequality.
  have h1 : η ^ m * (κ - η) ≤ ‖z - s‖ := by
    have := mul_le_mul_of_nonneg_right hηm hκpos.le
    rw [one_mul] at this
    linarith
  have h2 : η ^ m * (κ - η) * ‖F s‖ ≤ ‖z - s‖ * ‖F s‖ :=
    mul_le_mul_of_nonneg_right h1 hFspos.le
  have h3 : ‖z - s‖ * ‖F s‖ ≤ ‖z - s‖ * (‖F z‖ * Real.exp Y) :=
    mul_le_mul_of_nonneg_left hY (norm_nonneg _)
  have h4 : ‖z - s‖ * (‖F z‖ * Real.exp Y) = Real.exp Y * (‖z - s‖ * ‖F z‖) := by ring
  have hgoal : η ^ m * ((κ - η) * ‖F s‖) ≤ Real.exp Y * (‖z - s‖ * ‖F z‖) := by
    have := le_trans (le_trans h2 h3) (le_of_eq h4)
    nlinarith [this]
  rw [div_le_iff₀ hA, div_mul_eq_mul_div, le_div_iff₀ hB]
  exact hgoal

end Work.BW
