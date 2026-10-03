import Mathlib

/-!
# `exp (-2πi α z) = 1` when `z` is a limit point of the lattice `α⁻¹ℤ`

If the distance from `z` to the lattice `{(k : ℂ) / α | k : ℤ}` has infimum `0`, then `z` is
*equal* to a lattice point: distinct lattice points are at distance at least `1/‖α‖` from one
another, so a lattice point closer than `1/(2‖α‖)` is strictly the closest one, and an infimum
of `0` then forces the distance to that point to vanish.  Consequently `α z ∈ ℤ`, and
`exp (-2πi α z) = exp (-2πi k) = 1` for an integer `k`.
-/

namespace Work.Pert

theorem tauC_exp_one_of_iInf_eq_zero {α z : ℂ} (hα : α ≠ 0)
    (hd : (⨅ k : ℤ, dist z ((k : ℂ) / α)) = 0) :
    Complex.exp (-(2 * Real.pi * Complex.I * α * z)) = 1 := by
  have hαn : (0 : ℝ) < ‖α‖ := norm_pos_iff.mpr hα
  -- A lattice point lying at distance `< 1/(2‖α‖)` from `z` exists, because the infimum of the
  -- distances is `0 < 1/(2‖α‖)`.
  obtain ⟨k, hk⟩ : ∃ k : ℤ, dist z ((k : ℂ) / α) < 1 / (2 * ‖α‖) := by
    have hlt : (⨅ k : ℤ, dist z ((k : ℂ) / α)) < 1 / (2 * ‖α‖) := by
      rw [hd]; positivity
    exact exists_lt_of_ciInf_lt hlt
  have hk2 : 2 * dist z ((k : ℂ) / α) < 1 / ‖α‖ := by
    have h2 : (1 : ℝ) / (2 * ‖α‖) * 2 = 1 / ‖α‖ := by field_simp
    linarith [hk, h2]
  -- `k` is the closest lattice point, so it is a lower bound for all the distances, and the
  -- infimum `0` forces the distance `d = dist z (k/α)` to vanish.
  have hd0 : dist z ((k : ℂ) / α) = 0 := by
    have hbound : dist z ((k : ℂ) / α) ≤ ⨅ k' : ℤ, dist z ((k' : ℂ) / α) := by
      refine le_ciInf fun k' => ?_
      rcases eq_or_ne k' k with rfl | hne
      · exact le_rfl
      · -- distinct lattice points are at distance `≥ 1/‖α‖ = |k' - k| / ‖α‖`
        have hsep : (1 : ℝ) / ‖α‖ ≤ dist ((k' : ℂ) / α) ((k : ℂ) / α) := by
          have h1 : (1 : ℝ) ≤ ((|k' - k| : ℤ) : ℝ) := by
            exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hne)
          have hsub : (k' : ℂ) / α - (k : ℂ) / α = ((k' - k : ℤ) : ℂ) / α := by
            rw [← sub_div, ← Int.cast_sub]
          rw [dist_eq_norm, hsub, norm_div, Complex.norm_intCast, ← Int.cast_abs]
          exact div_le_div_of_nonneg_right h1 (norm_nonneg α)
        have htri : dist ((k' : ℂ) / α) ((k : ℂ) / α)
            ≤ dist ((k' : ℂ) / α) z + dist z ((k : ℂ) / α) := dist_triangle _ _ _
        rw [dist_comm ((k' : ℂ) / α) z] at htri
        linarith
    rw [hd] at hbound
    exact le_antisymm hbound dist_nonneg
  have hz : z = (k : ℂ) / α := dist_eq_zero.mp hd0
  -- hence `α z = k` is an integer and the exponential is `1`
  have hmul : α * z = (k : ℂ) := by rw [hz, ← mul_div_assoc, mul_div_cancel_left₀ _ hα]
  have h2pi : 2 * Real.pi * Complex.I * α * z = 2 * Real.pi * Complex.I * (k : ℂ) := by
    rw [show (2 : ℂ) * Real.pi * Complex.I * α * z
        = (2 * Real.pi * Complex.I) * (α * z) by ring, hmul]
  rw [h2pi]
  have harg : -(2 * Real.pi * Complex.I * (k : ℂ))
      = ((-k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [harg, Complex.exp_int_mul, Complex.exp_two_pi_mul_I, one_zpow]

end Work.Pert
