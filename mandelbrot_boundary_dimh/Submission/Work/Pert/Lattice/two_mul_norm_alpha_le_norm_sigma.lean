import Mathlib
import Submission.Work.Pert.norm_exp_sub_one_sub_id_le_sharp

namespace Work.Pert.Lattice

/-- **The rotation-number gap.** For `‖α‖ ≤ 1/64` one has
`4‖α‖ ≤ ‖1 - exp (2πi α)‖`.

The point is that `exp` moves a point of the disc of radius `2π/64 = π/32` by at least
`4‖α‖ ≈ (2/π)·π‖α‖`: with `z = 2πi α`, the sharp Taylor estimate
`‖exp z - 1 - z‖ ≤ (29/48)‖z‖²` (from `norm_exp_sub_one_sub_id_le_sharp`) gives
`‖1 - exp z‖ ≥ ‖z‖ - (29/48)‖z‖²`, and since `‖z‖ = 2π‖α‖ ≤ π/32`,
`‖z‖ - (29/48)‖z‖² ≥ 2π(1 - (29/48)(π/32))·‖α‖ = (2π - 29π²/768)‖α‖ > 4‖α‖`
because `π < 4` bounds `29π²/768 < 29/48` and `3 < π` gives `2π > 6`. -/
theorem four_mul_norm_alpha_le_norm_one_sub_exp {α : ℂ} (hα : ‖α‖ ≤ 1 / 64) :
    4 * ‖α‖ ≤ ‖1 - Complex.exp (2 * Real.pi * Complex.I * α)‖ := by
  set z : ℂ := 2 * Real.pi * Complex.I * α with hzdef
  have hzn : ‖z‖ = 2 * Real.pi * ‖α‖ := by
    rw [hzdef, norm_mul, norm_mul, norm_mul]
    simp [Complex.norm_I, Complex.norm_real, abs_of_pos Real.pi_pos]
  have ha : 0 ≤ ‖α‖ := norm_nonneg α
  have hz2 : ‖z‖ ≤ 1 / 2 := by
    rw [hzn]; nlinarith [Real.pi_lt_four, Real.pi_pos, hα, ha]
  have hb := Work.Pert.norm_exp_sub_one_sub_id_le_sharp hz2
  have htri : ‖z‖ ≤ ‖Complex.exp z - 1‖ + 29 / 48 * ‖z‖ ^ 2 := by
    have hsplit : z = (Complex.exp z - 1) - (Complex.exp z - 1 - z) := by ring
    calc ‖z‖ = ‖(Complex.exp z - 1) - (Complex.exp z - 1 - z)‖ := congrArg norm hsplit
      _ ≤ ‖Complex.exp z - 1‖ + ‖Complex.exp z - 1 - z‖ := norm_sub_le _ _
      _ ≤ ‖Complex.exp z - 1‖ + 29 / 48 * ‖z‖ ^ 2 := by linarith
  have harith : 4 * ‖α‖ ≤ ‖z‖ - 29 / 48 * ‖z‖ ^ 2 := by
    rw [hzn]
    have hπ2 : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_pos, Real.pi_lt_four]
    have ha2 : ‖α‖ ^ 2 ≤ (1 / 64) * ‖α‖ := by nlinarith [hα, ha]
    nlinarith [Real.pi_gt_three, hπ2, ha2, ha, hα]
  rw [norm_sub_rev]
  linarith

/-- From `1 - σ u₀ = exp (2πi α)` with `‖α‖ ≤ 1/64` and `‖u₀‖ ≤ 2`, the multiplier `σ` is
large compared with `α`: `2‖α‖ ≤ ‖σ‖`.

Indeed `σ u₀ = 1 - exp (2πi α)`, so `‖1 - exp (2πi α)‖ = ‖σ‖·‖u₀‖ ≤ 2‖σ‖`, while
`four_mul_norm_alpha_le_norm_one_sub_exp` gives `4‖α‖ ≤ ‖1 - exp (2πi α)‖`; halving gives the
claim. -/
theorem two_mul_norm_alpha_le_norm_sigma {α σ u₀ : ℂ} (hα64 : ‖α‖ ≤ 1 / 64)
    (hnorm : 1 - σ * u₀ = Complex.exp (2 * Real.pi * Complex.I * α))
    (hu₀ : ‖u₀‖ ≤ 2) : 2 * ‖α‖ ≤ ‖σ‖ := by
  have key : σ * u₀ = 1 - Complex.exp (2 * Real.pi * Complex.I * α) := by
    rw [← hnorm]; ring
  have h4 := four_mul_norm_alpha_le_norm_one_sub_exp hα64
  have hle : ‖σ * u₀‖ ≤ 2 * ‖σ‖ := by
    rw [norm_mul]
    nlinarith [hu₀, norm_nonneg σ]
  rw [key] at hle
  linarith

end Work.Pert.Lattice
