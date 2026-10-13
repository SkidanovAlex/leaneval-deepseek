import Mathlib

namespace Work.WilC4aP

/-- If a property holds eventually near the origin of `(Fin 1 → ℂ) × ℂ`, then it
holds on a small product box: there are radii `ρ, σ > 0` such that
`p (fun _ => z, w)` for all `‖z‖ < ρ`, `‖w‖ < σ`. -/
theorem exists_box_of_eventually_ambient {p : (Fin 1 → ℂ) × ℂ → Prop}
    (h : Filter.Eventually p (nhds (0 : (Fin 1 → ℂ) × ℂ))) :
    ∃ ρ σ : ℝ, 0 < ρ ∧ 0 < σ ∧
      ∀ z w : ℂ, ‖z‖ < ρ → ‖w‖ < σ →
        p (((fun _ : Fin 1 => z) : Fin 1 → ℂ), w) := by
  rw [Metric.eventually_nhds_iff] at h
  obtain ⟨ε, hεpos, hε⟩ := h
  refine ⟨ε, ε, hεpos, hεpos, fun z w hz hw => hε ?_⟩
  rw [dist_zero_right, Prod.norm_def]
  exact max_lt (by simpa using hz) hw

end Work.WilC4aP
