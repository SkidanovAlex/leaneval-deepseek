import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.FTS.PressureOn.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# A continuous `ℝ³ → ℝ³` map vanishing at infinity is bounded

This is the vector-valued counterpart of `Work.FTS.PressureOn.Auxiliary.tendsto_cocompact_bound_scalar`:
if `Φ : ℝ³ → ℝ³` is continuous and `Φ → 0` along the cocompact filter (i.e. `Φ` *vanishes at
infinity*), then `‖Φ‖` is bounded on all of `ℝ³`.

The argument has nothing to do with the codomain being a normed space: from `hΦ0` the set
`{x | ‖Φ x‖ < 1}` is a neighbourhood of infinity, so its complement is contained in a compact
`K`; `‖Φ‖` is bounded on the compact `K` by `IsCompact.exists_bound_of_continuousOn`, and the
two bounds are combined with `max`.
-/

namespace Work.FTS.PressureOn.Auxiliary

theorem cocompact_bound_vec {Φ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hΦ : Continuous Φ)
    (hΦ0 : Filter.Tendsto Φ (Filter.cocompact (EuclideanSpace ℝ (Fin 3))) (nhds 0)) :
    ∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C := by
  -- `hΦ0` gives that the preimage of the unit ball around `0` is a neighbourhood of infinity:
  -- its complement is contained in a compact set `K`.
  have hmem : {x : EuclideanSpace ℝ (Fin 3) | ‖Φ x‖ < 1}
      ∈ Filter.cocompact (EuclideanSpace ℝ (Fin 3)) := by
    have h := hΦ0 (Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin 3)) one_pos)
    rw [Filter.mem_map] at h
    rwa [show Φ ⁻¹' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1
        = {x : EuclideanSpace ℝ (Fin 3) | ‖Φ x‖ < 1} from by
      ext x; simp [Metric.mem_ball]] at h
  obtain ⟨K, hKc, hKsub⟩ := Filter.mem_cocompact.1 hmem
  -- `‖Φ‖` is bounded on the compact set `K` by continuity.
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn hΦ.continuousOn
  refine ⟨max M 1, fun x => ?_⟩
  by_cases hx : x ∈ K
  · exact (hM x hx).trans (le_max_left _ _)
  · have h := hKsub (by simpa using hx)
    exact (le_of_lt h).trans (le_max_right _ _)

end Work.FTS.PressureOn.Auxiliary
