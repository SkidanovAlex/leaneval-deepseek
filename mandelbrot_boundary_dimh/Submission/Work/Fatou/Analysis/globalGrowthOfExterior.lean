import Mathlib

namespace Work.Fatou.Analysis

/-- A continuous map `h : ℂ → ℂ` which grows at most like `c * ‖z‖ ^ n` on the exterior of
a ball of radius `R` grows at most like a constant times `(1 + ‖z‖) ^ n` everywhere: on the
closed ball `h` is bounded by compactness. -/
lemma globalGrowthOfExterior (h : ℂ → ℂ) (hcont : Continuous h) (n : ℕ) (c R : ℝ)
    (hc : 0 < c) (hR : 0 < R) (hbd : ∀ z : ℂ, R ≤ ‖z‖ → ‖h z‖ ≤ c * ‖z‖ ^ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ‖h z‖ ≤ C * (1 + ‖z‖) ^ n := by
  -- `‖h ·‖` is bounded on the compact closed ball of radius `R`.
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) R).bddAbove_image hcont.norm.continuousOn
  refine ⟨max M c, le_trans (le_of_lt hc) (le_max_right _ _), ?_⟩
  intro z
  have hC : 0 ≤ max M c := le_trans (le_of_lt hc) (le_max_right _ _)
  rcases lt_or_ge ‖z‖ R with hz | hz
  · -- interior of the ball: use the compactness bound, and `(1 + ‖z‖) ^ n ≥ 1`
    have hzK : z ∈ Metric.closedBall (0 : ℂ) R := by
      rw [Metric.mem_closedBall, dist_zero_right]; exact le_of_lt hz
    have hmem : ‖h z‖ ∈ (fun w : ℂ => ‖h w‖) '' Metric.closedBall (0 : ℂ) R := ⟨z, hzK, rfl⟩
    have h1 : (1 : ℝ) ≤ (1 + ‖z‖) ^ n := one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg z))
    calc ‖h z‖ ≤ M := hM hmem
      _ ≤ max M c := le_max_left _ _
      _ = max M c * 1 := (mul_one _).symm
      _ ≤ max M c * (1 + ‖z‖) ^ n := mul_le_mul_of_nonneg_left h1 hC
  · -- exterior: use the growth hypothesis and `‖z‖ ≤ 1 + ‖z‖`
    have h1 : ‖z‖ ^ n ≤ (1 + ‖z‖) ^ n :=
      pow_le_pow_left₀ (norm_nonneg z) (le_add_of_nonneg_left zero_le_one) n
    calc ‖h z‖ ≤ c * ‖z‖ ^ n := hbd z hz
      _ ≤ c * (1 + ‖z‖) ^ n := mul_le_mul_of_nonneg_left h1 (le_of_lt hc)
      _ ≤ max M c * (1 + ‖z‖) ^ n :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

end Work.Fatou.Analysis
