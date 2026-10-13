import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Topology

namespace Work.FTS.RegPkgGal.R7d

theorem quadrant_extend {α : ℝ → ℝ × ℝ} {σ T : ℝ} (hσ0 : 0 ≤ σ) (hσT : σ < T) (hαc : ContinuousOn α (Set.Icc 0 T)) (h1 : 0 < (α σ).1) (h2 : 0 < (α σ).2) (h3 : (α σ).2 < Real.pi / 2) : ∃ δ : ℝ, 0 < δ ∧ σ + δ ≤ T ∧ ∀ x ∈ Set.Ioo σ (σ + δ), 0 < (α x).1 ∧ 0 < (α x).2 ∧ (α x).2 < Real.pi / 2 := by
  -- The open set of pairs in the first quadrant below the line `y₂ = π/2`.
  have hopen : IsOpen {y : ℝ × ℝ | 0 < y.1 ∧ 0 < y.2 ∧ y.2 < Real.pi / 2} := by
    have h1o : IsOpen {y : ℝ × ℝ | 0 < y.1} := isOpen_lt continuous_const continuous_fst
    have h2o : IsOpen {y : ℝ × ℝ | 0 < y.2} := isOpen_lt continuous_const continuous_snd
    have h3o : IsOpen {y : ℝ × ℝ | y.2 < Real.pi / 2} :=
      isOpen_lt continuous_snd continuous_const
    exact h1o.inter (h2o.inter h3o)
  have hσmem : σ ∈ Set.Icc 0 T := ⟨hσ0, le_of_lt hσT⟩
  -- Continuity at `σ` along `[0,T]`: the preimage of the open set is a relative
  -- neighbourhood of `σ`.
  have hVw : α ⁻¹' {y : ℝ × ℝ | 0 < y.1 ∧ 0 < y.2 ∧ y.2 < Real.pi / 2} ∈
      𝓝[Set.Icc 0 T] σ :=
    (hαc.continuousWithinAt hσmem) (hopen.mem_nhds ⟨h1, h2, h3⟩)
  obtain ⟨ε, hεpos, hε⟩ := Metric.mem_nhdsWithin_iff.mp hVw
  -- Shrink so that the right endpoint `σ + δ` stays inside `[0,T]`.
  refine ⟨min (ε / 2) ((T - σ) / 2), ?_, ?_, ?_⟩
  · exact lt_min (by linarith) (by linarith)
  · have hle : min (ε / 2) ((T - σ) / 2) ≤ (T - σ) / 2 := min_le_right _ _
    linarith
  · intro x hx
    have hxIcc : x ∈ Set.Icc 0 T := by
      have hmm : min (ε / 2) ((T - σ) / 2) ≤ (T - σ) / 2 := min_le_right _ _
      constructor <;> linarith [hx.1, hx.2]
    have hxball : x ∈ Metric.ball σ ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith [hx.1])]
      have hmm : min (ε / 2) ((T - σ) / 2) ≤ ε / 2 := min_le_left _ _
      linarith [hx.2]
    exact hε ⟨hxball, hxIcc⟩

end Work.FTS.RegPkgGal.R7d
