import Mathlib

namespace Work.EQ

open Filter _root_.Topology

set_option linter.unusedVariables false in
/-- **Roots at the centre are small nearby.**  For `κ ≠ 0`, `k > 0` and `δ > 0` there is `ρ > 0`
such that every root of `u₁ + κ ζ^k = u` with `dist u u₁ < ρ` satisfies `dist ζ 0 < δ`. -/
theorem roots_small_of_centre_eq {κ u₁ : ℂ} (hκ : κ ≠ 0) {k : ℕ} (hk : 0 < k)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ u ζ : ℂ, dist u u₁ < ρ → u₁ + κ * ζ ^ k = u → dist ζ 0 < δ := by
  refine ⟨‖κ‖ * δ ^ k, ?_, ?_⟩
  · exact mul_pos (norm_pos_iff.mpr hκ) (pow_pos hδ k)
  · intro u ζ hu h
    -- From `u₁ + κ ζ^k = u` get `u - u₁ = κ ζ^k`.
    have hdiff : u - u₁ = κ * ζ ^ k := by rw [← h]; ring
    -- The hypothesis on `u` is exactly a bound on `‖κ‖ * ‖ζ‖^k`.
    have hu' : ‖u - u₁‖ < ‖κ‖ * δ ^ k := by
      rw [dist_eq_norm] at hu; exact hu
    rw [hdiff, norm_mul, norm_pow] at hu'
    have hz : ‖ζ‖ ^ k < δ ^ k := lt_of_mul_lt_mul_left hu' (norm_nonneg κ)
    -- `‖ζ‖ < δ` since `x ↦ x^k` is monotone on `[0,∞)` and `k ≥ 1`.
    have hnorm : ‖ζ‖ < δ := by
      by_contra hcon
      push Not at hcon
      have : δ ^ k ≤ ‖ζ‖ ^ k := pow_le_pow_left₀ hδ.le hcon k
      linarith
    simpa [dist_zero_right] using hnorm

end Work.EQ
