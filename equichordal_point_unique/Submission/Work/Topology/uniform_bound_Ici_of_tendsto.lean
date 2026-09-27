import Mathlib

namespace Work.Topology

/-- A function `ℝ → ℂ` that is continuous on `Ici S` and has a limit at `+∞` is bounded on `Ici S`. -/
theorem uniform_bound_Ici_of_tendsto {f : ℝ → ℂ} {S : ℝ} {u : ℂ}
    (hf : ContinuousOn f (Set.Ici S)) (hl : Filter.Tendsto f Filter.atTop (nhds u)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℝ, S ≤ s → ‖f s‖ ≤ B := by
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp
    (hl.eventually (Metric.ball_mem_nhds u (by norm_num : (0 : ℝ) < 1)))
  obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn
    (isCompact_Icc (a := S) (b := max S T))
    (hf.mono (fun x hx => hx.1))
  refine ⟨max C (‖u‖ + 1), le_trans (by positivity) (le_max_right _ _), ?_⟩
  intro s hs
  by_cases h : s ≤ max S T
  · exact le_trans (hC s ⟨hs, h⟩) (le_max_left _ _)
  · have hs' : T ≤ s := le_trans (le_max_right S T) (le_of_lt (not_le.mp h))
    have hd : dist (f s) u < 1 := Metric.mem_ball.mp (hT s hs')
    have h1 : ‖f s‖ ≤ dist (f s) u + ‖u‖ := by
      rw [dist_eq_norm]
      simpa using norm_add_le (f s - u) u
    have h3 : ‖f s‖ < ‖u‖ + 1 := by linarith
    exact le_trans h3.le (le_max_right _ _)

end Work.Topology
