import Mathlib

namespace Work.WilG4c

theorem contDiffAt_zero_local {n : ℕ} (g : (Fin (n + 1) → ℝ) → ℝ) (u : Fin (n + 1) → ℝ) :
    ContDiffAt ℝ 0 g u ↔ ∃ δ : ℝ, 0 < δ ∧ ∀ y : Fin (n + 1) → ℝ,
      (∀ j : Fin (n + 1), |y j - u j| < δ) → ContinuousAt g y := by
  rw [contDiffAt_zero]
  constructor
  · rintro ⟨s, hs, hcont⟩
    obtain ⟨δ, hδpos, hsub⟩ := Metric.mem_nhds_iff.mp hs
    refine ⟨δ, hδpos, fun y hy => ?_⟩
    have hyball : y ∈ Metric.ball u δ := by
      rw [Metric.mem_ball, dist_pi_lt_iff hδpos]
      intro j
      rw [Real.dist_eq]
      exact hy j
    exact hcont.continuousAt
      (Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hyball) hsub)
  · rintro ⟨δ, hδpos, hbox⟩
    refine ⟨Metric.ball u δ, Metric.ball_mem_nhds u hδpos, ?_⟩
    intro y hy
    refine (hbox y (fun j => ?_)).continuousWithinAt
    have h2 := (dist_pi_lt_iff hδpos).mp (Metric.mem_ball.mp hy) j
    rwa [Real.dist_eq] at h2

end Work.WilG4c
