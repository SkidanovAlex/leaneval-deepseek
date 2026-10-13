import Mathlib.Analysis.InnerProductSpace.PiL2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Auxiliary

theorem tendsto_cocompact_bound_scalar {g : EuclideanSpace ℝ (Fin 3) → ℝ} (hg : Continuous g)
    (hg0 : Filter.Tendsto g (Filter.cocompact (EuclideanSpace ℝ (Fin 3))) (nhds 0)) :
    (∃ C : ℝ, ∀ x, |g x| ≤ C) ∧
      (∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ x, R ≤ ‖x‖ → |g x| ≤ ε) := by
  -- From `hg0` we extract, for every `ε > 0`, that the set `{x | |g x| < ε}` belongs to
  -- the cocompact filter, i.e. its complement is contained in a compact set.
  have hbdd : ∃ C : ℝ, ∀ x, |g x| ≤ C := by
    have hmem : {x : EuclideanSpace ℝ (Fin 3) | |g x| < 1} ∈ Filter.cocompact _ := by
      have h := hg0 (Metric.ball_mem_nhds (0 : ℝ) one_pos)
      rw [Filter.mem_map] at h
      rwa [show g ⁻¹' Metric.ball (0 : ℝ) 1 = {x : EuclideanSpace ℝ (Fin 3) | |g x| < 1} from by
        ext x; simp [Metric.mem_ball]] at h
    obtain ⟨K, hKc, hKsub⟩ := Filter.mem_cocompact.1 hmem
    obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn hg.continuousOn
    refine ⟨max M 1, fun x => ?_⟩
    by_cases hx : x ∈ K
    · have h := hM x hx
      rw [Real.norm_eq_abs] at h
      exact h.trans (le_max_left _ _)
    · have h := hKsub (by simpa using hx)
      exact (le_of_lt h).trans (le_max_right _ _)
  refine ⟨hbdd, fun ε hε => ?_⟩
  have hmem : {x : EuclideanSpace ℝ (Fin 3) | |g x| < ε} ∈ Filter.cocompact _ := by
    have h := hg0 (Metric.ball_mem_nhds (0 : ℝ) hε)
    rw [Filter.mem_map] at h
    rwa [show g ⁻¹' Metric.ball (0 : ℝ) ε = {x : EuclideanSpace ℝ (Fin 3) | |g x| < ε} from by
      ext x; simp [Metric.mem_ball]] at h
  obtain ⟨K, hKc, hKsub⟩ := Filter.mem_cocompact.1 hmem
  obtain ⟨R, -, hR⟩ := hKc.isBounded.exists_pos_norm_lt
  refine ⟨R, fun x hx => ?_⟩
  have hxK : x ∉ K := fun h => absurd hx (not_le.2 (hR x h))
  exact le_of_lt (hKsub (by simpa using hxK))

end Work.FTS.PressureOn.Auxiliary
