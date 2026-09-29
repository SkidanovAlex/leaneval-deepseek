import Mathlib

namespace Work.C17g

set_option linter.unusedVariables false in
theorem convex_hull_segments {S : Set ℂ} (hS : Convex ℝ S) {z₀ : ℂ} (hz₀ : z₀ ∈ S)
    {z : ℂ} (hz : z ∈ S) {ρ : ℝ} (hρ : 0 < ρ) (hball : Metric.closedBall z ρ ⊆ S) :
    ∃ T : Set ℂ, IsCompact T ∧ T.Nonempty ∧ z₀ ∈ T ∧ Metric.ball z ρ ⊆ T ∧ T ⊆ S ∧
      (∀ w ∈ T, ∀ t ∈ Set.Icc (0:ℝ) 1, z₀ + t • (w - z₀) ∈ T) := by
  let T : Set ℂ :=
    (fun p : ℝ × ℂ => z₀ + p.1 • (p.2 - z₀)) '' (Set.Icc (0:ℝ) 1 ×ˢ Metric.closedBall z ρ)
  have hmem : ∀ w : ℂ, w ∈ T ↔
      ∃ t ∈ Set.Icc (0:ℝ) 1, ∃ v ∈ Metric.closedBall z ρ, z₀ + t • (v - z₀) = w := by
    intro w
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p.1, hp.1, p.2, hp.2, rfl⟩
    · rintro ⟨t, ht, v, hv, rfl⟩
      exact ⟨(t, v), ⟨ht, hv⟩, rfl⟩
  refine ⟨T, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (isCompact_Icc.prod (isCompact_closedBall z ρ)).image (by fun_prop)
  · exact ⟨z₀, (hmem z₀).2 ⟨0, ⟨le_rfl, zero_le_one⟩, z,
      Metric.mem_closedBall_self (le_of_lt hρ), by simp⟩⟩
  · exact (hmem z₀).2 ⟨0, ⟨le_rfl, zero_le_one⟩, z,
      Metric.mem_closedBall_self (le_of_lt hρ), by simp⟩
  · intro w hw
    exact (hmem w).2 ⟨1, ⟨zero_le_one, le_rfl⟩, w, Metric.ball_subset_closedBall hw, by simp⟩
  · rintro w hw
    obtain ⟨t, ht, v, hv, rfl⟩ := (hmem w).1 hw
    have hstar := hS.starConvex hz₀ (hball hv) (a := 1 - t) (b := t)
      (by linarith [ht.2]) ht.1 (by ring)
    convert hstar using 1
    rw [smul_sub, sub_smul, one_smul]
    abel
  · intro w hw t ht
    obtain ⟨s, hs, v, hv, rfl⟩ := (hmem w).1 hw
    refine (hmem _).2 ⟨t * s, ⟨mul_nonneg ht.1 hs.1, by nlinarith [ht.1, ht.2, hs.1, hs.2]⟩,
      v, hv, ?_⟩
    rw [add_sub_cancel_left, ← smul_smul]

end Work.C17g
