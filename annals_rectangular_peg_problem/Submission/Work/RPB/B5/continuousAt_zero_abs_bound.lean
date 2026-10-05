import Mathlib

namespace Work.RPB.B5

theorem continuousAt_zero_abs_bound {u : ℝ → ℝ} (hcont : ContinuousAt u 0) (hu0 : u 0 = 0)
    {ε : ℝ} (hε : 0 < ε) : ∃ δ : ℝ, 0 < δ ∧ ∀ σ : ℝ, |σ| < δ → |u σ| < ε := by
  have h1 : u ⁻¹' Metric.ball (u 0) ε ∈ nhds (0 : ℝ) :=
    hcont (Metric.ball_mem_nhds (u 0) hε)
  rw [Metric.mem_nhds_iff] at h1
  obtain ⟨δ', hδ'pos, hδ'sub⟩ := h1
  refine ⟨δ', hδ'pos, fun σ hσ => ?_⟩
  have hmem : σ ∈ Metric.ball (0 : ℝ) δ' := by
    simpa [Real.dist_eq, abs_sub_comm] using hσ
  have h2 : u σ ∈ Metric.ball (u 0) ε := hδ'sub hmem
  rw [Metric.mem_ball, hu0] at h2
  simpa [Real.dist_eq, abs_sub_comm] using h2

end Work.RPB.B5
