import Mathlib

namespace Work.WilE9G.Sard

/-- **One plus a rank-one perturbation is a continuous linear equivalence.**  For a continuous
linear functional `u` and a vector `s` with `1 + u s ≠ 0`, the map `x ↦ x + (u x) • s` is a
continuous linear equivalence of `E` with itself. -/
theorem smulRight_continuousLinearEquiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : E →L[ℝ] ℝ) (s : E) (h : 1 + u s ≠ 0) :
    ∃ e : E ≃L[ℝ] E, (e : E →L[ℝ] E) = 1 + u.smulRight s := by
  -- The inverse of `1 + u.smulRight s` is the rank-one perturbation
  -- `1 - (1 + u s)⁻¹ • u.smulRight s` (Sherman–Morrison in rank one).
  refine ⟨ContinuousLinearEquiv.equivOfInverse (1 + u.smulRight s)
    (1 - (1 + u s)⁻¹ • u.smulRight s) ?_ ?_, ?_⟩
  · intro x
    simp only [sub_apply, add_apply, one_apply_eq_self, smul_apply,
      ContinuousLinearMap.smulRight_apply, map_add, map_smul, smul_smul]
    simp only [smul_sub, smul_smul]
    match_scalars <;> field_simp <;> ring
  · intro x
    simp only [sub_apply, add_apply, one_apply_eq_self, smul_apply,
      ContinuousLinearMap.smulRight_apply, smul_smul]
    simp only [map_sub, map_smul, smul_eq_mul]
    match_scalars <;> field_simp <;> ring
  · rw [ContinuousLinearEquiv.toContinuousLinearMap_equivOfInverse]

end Work.WilE9G.Sard
