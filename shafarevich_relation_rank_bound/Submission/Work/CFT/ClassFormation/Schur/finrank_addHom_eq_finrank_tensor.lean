import Mathlib

namespace Work.CFT.ClassFormation.Schur

/-- Additive homomorphisms into `ZMod p` are the same functions as `ℤ`-linear maps into
`ZMod p`, and the pointwise `ZMod p`-module structures coincide. -/
private noncomputable def addHomToIntLinear (p : ℕ) (A : Type) [AddCommGroup A] :
    (A →+ ZMod p) ≃ₗ[ZMod p] (A →ₗ[ℤ] ZMod p) where
  toFun f := f.toIntLinearMap
  invFun g := g.toAddMonoidHom
  map_add' f g := by ext a; rfl
  map_smul' c f := by ext a; rfl
  left_inv f := by ext a; rfl
  right_inv g := by ext a; rfl

/-- The extension-of-scalars adjunction `Hom_ℤ(A, 𝔽_p) ≅ Hom_{𝔽_p}(𝔽_p ⊗_ℤ A, 𝔽_p)`, as a
`𝔽_p`-linear equivalence. -/
private noncomputable def tensorHomAdjEquiv (p : ℕ) (A : Type) [AddCommGroup A] :
    (A →+ ZMod p) ≃ₗ[ZMod p] (TensorProduct ℤ (ZMod p) A →ₗ[ZMod p] ZMod p) :=
  (addHomToIntLinear p A).trans
    ((LinearMap.ringLmapEquivSelf (ZMod p) (ZMod p) (A →ₗ[ℤ] ZMod p)).symm.trans
      (TensorProduct.AlgebraTensorModule.lift.equiv ℤ (ZMod p) (ZMod p) (ZMod p) A (ZMod p)))

theorem finrank_addHom_eq_finrank_tensor (p : ℕ) [Fact p.Prime] (A : Type) [AddCommGroup A] :
    Module.finrank (ZMod p) (A →+ ZMod p) =
      Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) A) := by
  rw [← Subspace.dual_finrank_eq (K := ZMod p) (V := TensorProduct ℤ (ZMod p) A)]
  exact LinearEquiv.finrank_eq (tensorHomAdjEquiv p A)

end Work.CFT.ClassFormation.Schur
