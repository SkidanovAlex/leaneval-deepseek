import Mathlib
import Submission.Work.Pert.norm_one_sub_exp_two_pi_I_mul_ge

namespace Work.Pert

/-- **Global lattice lower bound for the `τ_f` denominator.**  If `α ≠ 0` and `z` is at positive
distance `d = ⨅ k : ℤ, dist z (k / α)` from the lattice `ℤ / α`, then

  `(3 / 4) * min 1 (‖α‖ d) ≤ ‖1 - exp (-2πi α z)‖`.

This is the sharp form of the elementary estimate used to bound the denominator of the universal
cover `τ_f = σ / (1 - exp (-2πi α z))` near the lattice: with `ξ := -α z` and `c := ‖α‖ d`, the
lattice hypothesis `c ≤ ‖k - α z‖` is exactly `dist (α z, ℤ) ≥ c`, and the estimate is
`Work.Pert.norm_one_sub_exp_two_pi_I_mul_ge`. -/
theorem tauC_denom_lower_global {α z : ℂ} (hα : α ≠ 0)
    (hd : 0 < ‖α‖ * (⨅ k : ℤ, dist z ((k : ℂ) / α))) :
    (3 / 4) * min 1 (‖α‖ * (⨅ k : ℤ, dist z ((k : ℂ) / α)))
      ≤ ‖1 - Complex.exp (-(2 * Real.pi * Complex.I * α * z))‖ := by
  set d : ℝ := ⨅ k : ℤ, dist z ((k : ℂ) / α) with hd_def
  have hc : 0 < ‖α‖ * d := by rw [hd_def]; exact hd
  -- the lattice hypothesis of `norm_one_sub_exp_two_pi_I_mul_ge`, with `ξ = -α z`
  have hbd : ∀ k : ℤ, ‖α‖ * d ≤ ‖(-α * z) + (k : ℂ)‖ := by
    intro k
    have hle : d ≤ dist z ((k : ℂ) / α) := by
      rw [hd_def]
      exact ciInf_le ⟨0, by rintro b ⟨j, rfl⟩; exact dist_nonneg⟩ k
    have h1 : ‖α‖ * d ≤ ‖α‖ * dist z ((k : ℂ) / α) :=
      mul_le_mul_of_nonneg_left hle (norm_nonneg α)
    have h2 : ‖α‖ * dist z ((k : ℂ) / α) = ‖(-α * z) + (k : ℂ)‖ := by
      rw [dist_eq_norm, ← norm_mul]
      rw [show α * (z - (k : ℂ) / α) = -((-α * z) + (k : ℂ)) by
            field_simp; ring, norm_neg]
    rw [h2] at h1; exact h1
  have hmain := norm_one_sub_exp_two_pi_I_mul_ge (-α * z) (‖α‖ * d) hc hbd
  have harg : 2 * (Real.pi : ℂ) * Complex.I * (-α * z)
      = -(2 * Real.pi * Complex.I * α * z) := by ring
  rw [harg] at hmain
  exact hmain

end Work.Pert
