import Mathlib
import Submission.Work.ORHomAlg.Map

namespace Work.ORHomAlg.Exactness

/-- Right exactness of the balanced tensor product: `M ⊠[R] -` preserves surjectivity. -/
theorem lTensor_surjective {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module Rᵐᵒᵖ M]
    {N : Type*} [AddCommGroup N] [Module R N] {N' : Type*} [AddCommGroup N'] [Module R N']
    (g : N →ₗ[R] N') (hg : Function.Surjective g) :
    Function.Surjective (Work.ORHomAlg.BalancedTensor.lTensor (M := M) g) := by
  intro x
  induction x using Work.ORHomAlg.BalancedTensor.induction_on with
  | H0 => exact ⟨0, map_zero _⟩
  | Hadd a b ha hb =>
      obtain ⟨a', ha'⟩ := ha
      obtain ⟨b', hb'⟩ := hb
      exact ⟨a' + b', by rw [map_add, ha', hb']⟩
  | Htmul m n' =>
      obtain ⟨n, rfl⟩ := hg n'
      exact ⟨Work.ORHomAlg.BalancedTensor.tmul R m n, by simp⟩

end Work.ORHomAlg.Exactness
