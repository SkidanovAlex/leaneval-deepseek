import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The inverse coordinate map of `Module.finBasis` is bounded

Layer B reads chart components in the flat coordinates `Fin n → ℝ` via
`(Module.finBasis ℝ E).equivFun : E ≃ₗ[ℝ] (Fin n → ℝ)`.  For the localisation and periodisation
steps one needs the (two-sided) comparison of the norm of `E` with the sup norm on `Fin n → ℝ`;
this file provides the easy direction, `‖equivFun.symm u‖ ≤ C ‖u‖`.
-/

namespace Work.Diff.STE

theorem exists_norm_bound_finBasis {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] :
    ∃ C : ℝ, 0 < C ∧ ∀ u : Fin (Module.finrank ℝ E) → ℝ,
      ‖(Module.finBasis ℝ E).equivFun.symm u‖ ≤ C * ‖u‖ := by
  classical
  let L : (Fin (Module.finrank ℝ E) → ℝ) →ₗ[ℝ] E :=
    ((Module.finBasis ℝ E).equivFun.symm : (Fin (Module.finrank ℝ E) → ℝ) ≃ₗ[ℝ] E)
  let f : (Fin (Module.finrank ℝ E) → ℝ) →L[ℝ] E := L.toContinuousLinearMap
  refine ⟨max ‖f‖ 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun u => ?_⟩
  calc ‖(Module.finBasis ℝ E).equivFun.symm u‖ = ‖f u‖ := rfl
    _ ≤ ‖f‖ * ‖u‖ := f.le_opNorm u
    _ ≤ max ‖f‖ 1 * ‖u‖ := by
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg u)

end Work.Diff.STE
