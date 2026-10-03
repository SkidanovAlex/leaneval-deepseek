import Mathlib
import Submission.Work.ORCoherence.Defs
import Submission.Work.ORCoherence.Map

namespace Work.ORCoherence.Tensor

theorem balanced_map_comp {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    {M M' M'' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    [AddCommGroup M''] [Module R M''] (g : M →ₗ[R] M') (g' : M' →ₗ[R] M'') :
    Balanced.map f (g' ∘ₗ g) = (Balanced.map f g') ∘ₗ (Balanced.map f g) := by
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ y =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul s m =>
        change (Balanced.map f (g' ∘ₗ g)) (Balanced.tmul f s m) =
          (Balanced.map f g') ((Balanced.map f g) (Balanced.tmul f s m))
        rw [Balanced.map_tmul, Balanced.map_tmul, Balanced.map_tmul]
        rfl
    | add a b ha hb => simp [map_add, ha, hb]

end Work.ORCoherence.Tensor
