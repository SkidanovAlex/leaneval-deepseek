import Mathlib
import Submission.Work.ORLyndon.BalTensorQuotDefs

universe u

namespace Work.ORLyndon

/-- The backward map of the identification `X ⧸ X·I ≅ X ⊗_R (R/I)`: the map
`x + X·I ↦ x ⊗ 1`.  It is well defined because `x·i ⊗ 1 = x ⊗ (i·1) = x ⊗ 0 = 0` for `i ∈ I`. -/
theorem balTensor_bwdMap (R : Type u) [Ring R] (I : Ideal R) (X : Type u) [AddCommGroup X]
    [Module Rᵐᵒᵖ X] :
    ∃ g : (X ⧸ Work.ORLyndon.balImage R I X) →+ Work.ORFlatness.BalTensor R X (R ⧸ I),
      ∀ x : X, g (Submodule.Quotient.mk x) = Work.ORFlatness.BalTensor.mk R x 1 := by
  -- The ℤ-linear map `x ↦ x ⊗ 1`, which is to descend to the quotient `X ⧸ X·I`.
  let f : X →ₗ[ℤ] Work.ORFlatness.BalTensor R X (R ⧸ I) :=
    (Work.ORFlatness.BalTensor.mkLeft R (1 : R ⧸ I)).toIntLinearMap
  have hf : ∀ x : X, f x = Work.ORFlatness.BalTensor.mk R x 1 := fun _ => rfl
  -- `X·I` lies in the kernel, by the balancing relation.
  have hker : Work.ORLyndon.balImage R I X ≤ f.ker := by
    rw [Work.ORLyndon.balImage_le_iff]
    intro x i
    rw [LinearMap.mem_ker, hf, Work.ORFlatness.BalTensor.mk_smul_right]
    have h : (i : R) • (1 : R ⧸ I) = 0 := by
      change Submodule.Quotient.mk ((i : R) • (1 : R)) = (0 : R ⧸ I)
      rw [Submodule.Quotient.mk_eq_zero]
      simpa using i.2
    rw [h, Work.ORFlatness.BalTensor.mk_zero_right]
  refine ⟨(Submodule.liftQ (Work.ORLyndon.balImage R I X) f hker).toAddMonoidHom, ?_⟩
  intro x
  rw [LinearMap.toAddMonoidHom_coe, Submodule.liftQ_apply]
  exact hf x

end Work.ORLyndon
