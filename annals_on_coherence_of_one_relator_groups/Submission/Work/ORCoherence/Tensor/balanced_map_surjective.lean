import Mathlib
import Submission.Work.ORCoherence.Defs
import Submission.Work.ORCoherence.Map

open scoped TensorProduct

namespace Work.ORCoherence.Tensor

open Work.ORCoherence

/-- The underlying `ℤ`-linear map of `balancedMapAux g` is the tensor product of the
identity on `S` with `g`, so it is surjective whenever `g` is. -/
theorem balancedMapAux_surjective {R S : Type*} [Ring R] [Ring S]
    {M M' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    (g : M →ₗ[R] M') (hg : Function.Surjective g) :
    Function.Surjective (balancedMapAux (S := S) g : S ⊗[ℤ] M →ₗ[S] S ⊗[ℤ] M') := by
  change Function.Surjective
    (TensorProduct.map (LinearMap.id : S →ₗ[ℤ] S) (g.restrictScalars ℤ))
  exact TensorProduct.map_surjective (fun x => ⟨x, rfl⟩) (fun x => hg x)

theorem balanced_map_surjective {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    {M M' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    (g : M →ₗ[R] M') (hg : Function.Surjective g) : Function.Surjective (Balanced.map f g) := by
  have hAux := balancedMapAux_surjective (S := S) g hg
  have hrange : (Balanced.map f g).range = ⊤ := by
    rw [Balanced.map, Submodule.range_mapQ]
    rw [LinearMap.range_eq_top.mpr hAux]
    simp
  exact LinearMap.range_eq_top.mp hrange

end Work.ORCoherence.Tensor
