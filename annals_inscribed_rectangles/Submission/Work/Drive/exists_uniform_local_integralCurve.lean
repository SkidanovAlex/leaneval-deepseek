import Mathlib

namespace Work.Drive

open Set Metric

/-- A globally Lipschitz vector field `w` on a complete normed space, with a uniform norm bound
`C` on its values, admits integral curves starting at every point `x₀ ∈ E`, all defined on one
common open interval `(-ε, ε)` around `0`, where `ε > 0` depends only on the Lipschitz constant
and the norm bound (not on `x₀`).

This is the uniform-in-the-initial-point form of the Picard--Lindelöf (Cauchy--Lipschitz)
theorem: we feed the global data into `IsPicardLindelof.of_time_independent` with a fixed radius
`C + 1`, initial deviation `0` and time half-width `1`, so that the time-size condition
`C * 1 ≤ (C + 1) - 0` holds for every initial point. -/
theorem exists_uniform_local_integralCurve {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {w : E → E} {K : NNReal} {C : NNReal}
    (hK : LipschitzWith K w) (hC : ∀ x, ‖w x‖ ≤ (C : ℝ)) :
    ∃ ε > 0, ∀ x₀ : E, ∃ γ : ℝ → E, γ 0 = x₀ ∧
      IsIntegralCurveOn γ (fun _ y => w y) (Set.Ioo (-ε) ε) := by
  refine ⟨1, one_pos, fun x₀ => ?_⟩
  have hpl : IsPicardLindelof (fun _ : ℝ => w) (tmin := (-1 : ℝ)) (tmax := 1)
      (t₀ := ⟨0, by norm_num⟩) x₀ (C + 1) 0 C K := by
    refine IsPicardLindelof.of_time_independent ?_ ?_ ?_
    · intro x _
      exact hC x
    · exact hK.lipschitzOnWith
    · simp only [sub_zero, zero_sub, neg_neg, max_self, mul_one, NNReal.coe_add,
        NNReal.coe_one, NNReal.coe_zero]
      linarith
  obtain ⟨α, hα0, hα⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨α, hα0, fun t ht =>
    (hα t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2) |>.hasDerivWithinAt⟩

end Work.Drive
