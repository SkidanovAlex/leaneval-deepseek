import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Series

/-- If `f` is continuous on `[0, π/2]` and vanishes at both endpoints, then `f` is uniformly
small on a pair of boundary layers `[0, ρ] ∪ [π/2 - ρ, π/2]` of the interval.  This is just
the one-sided continuity of `f` at the two endpoints. -/
theorem exists_layer_small (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc 0 (Real.pi / 2)))
    (h0 : f 0 = 0) (h1 : f (Real.pi / 2) = 0) :
    ∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧ ∀ θ : ℝ,
      (θ ∈ Set.Icc 0 ρ ∨ θ ∈ Set.Icc (Real.pi / 2 - ρ) (Real.pi / 2)) → |f θ| < ε := by
  intro ε hε
  have hπ : 0 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hmem0 : (0 : ℝ) ∈ Set.Icc 0 (Real.pi / 2) := ⟨le_refl 0, hπ.le⟩
  have hmem1 : Real.pi / 2 ∈ Set.Icc 0 (Real.pi / 2) := ⟨hπ.le, le_refl _⟩
  obtain ⟨δ₁, hδ₁, hb₁⟩ := (Metric.continuousWithinAt_iff.mp (hf.continuousWithinAt hmem0)) ε hε
  obtain ⟨δ₂, hδ₂, hb₂⟩ := (Metric.continuousWithinAt_iff.mp (hf.continuousWithinAt hmem1)) ε hε
  set ρ : ℝ := min (min (δ₁ / 2) (δ₂ / 2)) (Real.pi / 2) with hρdef
  have hρ1 : ρ ≤ δ₁ / 2 := hρdef ▸ le_trans (min_le_left _ _) (min_le_left _ _)
  have hρ2 : ρ ≤ δ₂ / 2 := hρdef ▸ le_trans (min_le_left _ _) (min_le_right _ _)
  have hρπ : ρ ≤ Real.pi / 2 := hρdef ▸ min_le_right _ _
  have hρpos : 0 < ρ := hρdef ▸ lt_min (lt_min (by linarith) (by linarith)) hπ
  refine ⟨ρ, hρpos, ?_⟩
  intro θ hθ
  rcases hθ with ⟨hθ0, hθρ⟩ | ⟨hθa, hθb⟩
  · -- left layer: `θ` is close to `0`
    have hs : θ ∈ Set.Icc 0 (Real.pi / 2) := ⟨hθ0, le_trans hθρ hρπ⟩
    have hd : dist θ 0 < δ₁ := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hθ0]
      linarith [le_trans hθρ hρ1]
    have := hb₁ hs hd
    rw [h0, Real.dist_eq, sub_zero] at this
    exact this
  · -- right layer: `θ` is close to `π/2`
    have hs : θ ∈ Set.Icc 0 (Real.pi / 2) := ⟨by linarith [hθa, hρπ], hθb⟩
    have hd : dist θ (Real.pi / 2) < δ₂ := by
      rw [Real.dist_eq, abs_of_nonpos (by linarith : θ - Real.pi / 2 ≤ 0),
        show -(θ - Real.pi / 2) = Real.pi / 2 - θ from by ring]
      have : Real.pi / 2 - θ ≤ ρ := by linarith
      linarith [hρ2, hδ₂]
    have := hb₂ hs hd
    rw [h1, Real.dist_eq, sub_zero] at this
    exact this

end Work.FTS.PhiStar.Series
