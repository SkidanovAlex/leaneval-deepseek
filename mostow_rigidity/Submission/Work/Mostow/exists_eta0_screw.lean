import Mathlib
set_option linter.unusedVariables false

namespace Work.Mostow

/-- For `r ≥ 2`, a constant `K₀ > 0` and `V > 0` there is a threshold `η₀ > 0` (depending only on
`r, K₀, V`) such that the "star inequality" of `Work.Mostow.screwCountingCard` holds with
`ρ_* = 1`, `N = 1` and the minimal admissible `δ := 2 sinh (η/2) + 4√r·η`:
`K₀ · V · √r · 2^r · (4π√r)^r · δ^{r-1} < 1` for every `η ∈ (0, η₀]`.  This is the arithmetic that
lets the geodesic-stratum screw step choose its scale `η₀` independently of the lattice. -/
theorem exists_eta0_screw (r : ℕ) (hr : 2 ≤ r) (K₀ V : ℝ) (hK₀ : 0 < K₀) (hV : 0 < V) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ →
      K₀ * V * Real.sqrt (r : ℝ) * 2 ^ r * (4 * Real.pi * Real.sqrt (r : ℝ)) ^ r *
        (2 * Real.sinh (η / 2) + 4 * Real.sqrt (r : ℝ) * η) ^ (r - 1) < 1 := by
  -- The left-hand side is a continuous function of `η` which vanishes at `η = 0` (here `r - 1 ≥ 1`
  -- is used), so it is `< 1` on a neighbourhood of `0`.  We extract the corresponding radius.
  let f : ℝ → ℝ := fun η =>
    K₀ * V * Real.sqrt (r : ℝ) * 2 ^ r * (4 * Real.pi * Real.sqrt (r : ℝ)) ^ r *
      (2 * Real.sinh (η / 2) + 4 * Real.sqrt (r : ℝ) * η) ^ (r - 1)
  have hcont : Continuous f := by
    unfold f
    fun_prop
  have hf0val : f 0 = 0 := by
    have hr1 : r - 1 ≠ 0 := by omega
    simp [f, Real.sinh_zero, zero_pow hr1]
  obtain ⟨δ, hδpos, hδ⟩ := (Metric.continuousAt_iff.mp hcont.continuousAt) 1 one_pos
  refine ⟨δ / 2, by positivity, ?_⟩
  intro η hη hηle
  have hdist : dist η 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hη]; linarith
  have h1 : dist (f η) (f 0) < 1 := hδ hdist
  rw [hf0val, Real.dist_eq, sub_zero] at h1
  exact (abs_lt.mp h1).2

end Work.Mostow
