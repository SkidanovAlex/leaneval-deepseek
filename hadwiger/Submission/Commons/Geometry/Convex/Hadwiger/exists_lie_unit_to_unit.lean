import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

noncomputable section

namespace Commons.Geometry.Convex.Hadwiger

/-- In a real inner product space, any unit vector can be carried to the unit vector in the
direction of a given nonzero vector by a linear isometry of the space. -/
theorem exists_lie_unit_to_unit {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V] [FiniteDimensional ℝ V]
    (a : V) (ha : ‖a‖ = 1) (b : V) (hb : b ≠ 0) :
    ∃ ρ : V ≃ₗᵢ[ℝ] V, ρ a = ‖b‖⁻¹ • b := by
  let c : V := ‖b‖⁻¹ • b
  have hc_norm : ‖c‖ = 1 := by
    dsimp [c]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg b)]
    exact inv_mul_cancel₀ (by simpa using (norm_ne_zero_iff.mpr hb))
  have hnorm : ‖a‖ = ‖c‖ := by rw [ha, hc_norm]
  refine ⟨Submodule.reflection (ℝ ∙ (a - c))ᗮ, ?_⟩
  change Submodule.reflection (ℝ ∙ (a - c))ᗮ a = c
  exact Submodule.reflection_sub hnorm

end Commons.Geometry.Convex.Hadwiger
