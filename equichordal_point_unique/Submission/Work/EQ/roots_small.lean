import Mathlib

namespace Work.EQ

/-- The roots of `u₀ + κ ζ^k = u` are uniformly small when `u` is close to `u₀`. -/
theorem roots_small {κ u₀ : ℂ} (hκ : κ ≠ 0) {k : ℕ} (hk : 0 < k) {r : ℝ} (hr : 0 < r) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ u ∈ Metric.ball u₀ ρ, u ≠ u₀ → ∀ ζ : ℂ, ζ ≠ 0 →
      u₀ + κ * ζ ^ k = u → ‖ζ‖ < r := by
  refine ⟨r ^ k * ‖κ‖, mul_pos (pow_pos hr k) (norm_pos_iff.mpr hκ), ?_⟩
  intro u hu _ ζ _ h
  -- `u ∈ ball u₀ ρ` unfolds to `‖u - u₀‖ < ρ`
  rw [Metric.mem_ball, dist_eq_norm] at hu
  -- the equation solved for the power
  have hkey : κ * ζ ^ k = u - u₀ := by rw [← h]; ring
  -- take norms: `‖κ‖ * ‖ζ‖ ^ k = ‖u - u₀‖`
  have hunorm : ‖κ‖ * ‖ζ‖ ^ k = ‖u - u₀‖ := by
    have h1 := congrArg norm hkey
    simpa [norm_mul, norm_pow] using h1
  have hnorm : ‖ζ‖ ^ k = ‖u - u₀‖ / ‖κ‖ := by
    rw [eq_div_iff (norm_ne_zero_iff.mpr hκ), mul_comm]
    exact hunorm
  -- hence `‖ζ‖ ^ k < r ^ k`, since `‖u - u₀‖ < r ^ k * ‖κ‖`
  have hlt : ‖ζ‖ ^ k < r ^ k := by
    rw [hnorm, div_lt_iff₀ (norm_pos_iff.mpr hκ)]
    exact hu
  -- and taking `k`-th roots gives the claim
  exact (pow_lt_pow_iff_left₀ (norm_nonneg ζ) (le_of_lt hr) (Nat.pos_iff_ne_zero.mp hk)).mp hlt

end Work.EQ
