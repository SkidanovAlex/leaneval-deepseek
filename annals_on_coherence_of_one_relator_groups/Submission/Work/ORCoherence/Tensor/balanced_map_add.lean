import Mathlib
import Submission.Work.ORCoherence.Defs
import Submission.Work.ORCoherence.Map

set_option autoImplicit false

open scoped TensorProduct

namespace Work.ORCoherence.Tensor

/-- The auxiliary linear map defining functoriality of the balanced tensor product is
additive in the linear map it is built from. -/
theorem balancedMapAux_add {R S : Type*} [Ring R] [Ring S]
    {M M' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    (g g' : M →ₗ[R] M') :
    balancedMapAux (S := S) (g + g') =
      balancedMapAux (S := S) g + balancedMapAux (S := S) g' := by
  apply LinearMap.ext
  intro x
  show TensorProduct.map (LinearMap.id : S →ₗ[ℤ] S) ((g + g').restrictScalars ℤ) x =
    TensorProduct.map (LinearMap.id : S →ₗ[ℤ] S) (g.restrictScalars ℤ) x +
    TensorProduct.map (LinearMap.id : S →ₗ[ℤ] S) (g'.restrictScalars ℤ) x
  rw [LinearMap.restrictScalars_add, TensorProduct.map_add_right, LinearMap.add_apply]

theorem balanced_map_add {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    {M M' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    (g g' : M →ₗ[R] M') : Balanced.map f (g + g') = Balanced.map f g + Balanced.map f g' := by
  have h1 : balancedMapAux (S := S) (g + g') =
      balancedMapAux (S := S) g + balancedMapAux (S := S) g' := balancedMapAux_add g g'
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ y =>
    simp only [Balanced.map, LinearMap.add_apply, Submodule.mapQ_apply]
    rw [h1, LinearMap.add_apply, Submodule.Quotient.mk_add]

end Work.ORCoherence.Tensor
