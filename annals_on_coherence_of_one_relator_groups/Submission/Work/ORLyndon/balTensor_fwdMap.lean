import Mathlib
import Submission.Work.ORLyndon.BalTensorQuotDefs

/-!
# The forward map `X × (R ⧸ I) → X ⧸ X·I`

For a ring `R`, an ideal `I ≤ R` and a right `R`-module `X`, we construct the `ℤ`-bilinear map
`balTensor_fwdMap`: it sends `(x, r)` to the class of `x·r` in `X ⧸ X·I`, where
`X·I = Work.ORLyndon.balImage R I X`.  This is the forward half of the identification of
`X ⧸ X·I` with the balanced tensor product `X ⊗_R (R ⧸ I)`
(`Work.ORLyndon.balTensor_quot_equiv`).

The map is well defined on `R ⧸ I` because `x·I ⊆ X·I` by construction: this is the single
point where the definition of `balImage` is used.
-/

set_option autoImplicit false

open MulOpposite

universe u

namespace Work.ORLyndon

/-- The underlying function of the forward map, on a fixed `x`: the class of `r : R` in `R ⧸ I`
is sent to the class of `op r • x` in `X ⧸ X·I`. -/
noncomputable def balFun (R : Type u) [Ring R] (I : Ideal R) (X : Type u) [AddCommGroup X]
    [Module Rᵐᵒᵖ X] (x : X) : R ⧸ I → (X ⧸ balImage R I X) :=
  fun q => Quotient.liftOn q (fun r => Submodule.Quotient.mk (op r • x))
    (fun a b hab => by
      have hab' : a - b ∈ (I : Submodule R R) := (Submodule.quotientRel_def _).mp hab
      rw [Submodule.Quotient.eq]
      rw [← sub_smul (op a) (op b) x, ← op_sub]
      exact Submodule.subset_span ⟨(x, ⟨a - b, hab'⟩), rfl⟩)

/-- The defining property of `balFun`: on the class of `r`, it is the class of `op r • x`. -/
lemma balFun_mk (R : Type u) [Ring R] (I : Ideal R) (X : Type u) [AddCommGroup X]
    [Module Rᵐᵒᵖ X] (x : X) (r : R) :
    balFun R I X x (Submodule.Quotient.mk r) = Submodule.Quotient.mk (op r • x) := by
  rw [balFun]
  exact Quotient.liftOn_mk _ _ r

/-- For fixed `x`, the forward map is an additive homomorphism in the `R ⧸ I` variable. -/
noncomputable def balAux (R : Type u) [Ring R] (I : Ideal R) (X : Type u) [AddCommGroup X]
    [Module Rᵐᵒᵖ X] (x : X) : R ⧸ I →+ (X ⧸ balImage R I X) where
  toFun := balFun R I X x
  map_zero' := by
    rw [← Submodule.Quotient.mk_zero (p := (I : Submodule R R))]
    rw [balFun_mk, op_zero, zero_smul, Submodule.Quotient.mk_zero]
  map_add' := fun a b => by
    obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective (p := (I : Submodule R R)) a
    obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective (p := (I : Submodule R R)) b
    rw [← Submodule.Quotient.mk_add (p := (I : Submodule R R)), balFun_mk, balFun_mk, balFun_mk,
      op_add, add_smul, Submodule.Quotient.mk_add]

/-- For fixed `x`, the forward map as a `ℤ`-linear map in the `R ⧸ I` variable. -/
noncomputable def balAuxL (R : Type u) [Ring R] (I : Ideal R) (X : Type u) [AddCommGroup X]
    [Module Rᵐᵒᵖ X] (x : X) : R ⧸ I →ₗ[ℤ] (X ⧸ balImage R I X) :=
  AddMonoidHom.toIntLinearMap (balAux R I X x)

lemma balAuxL_mk (R : Type u) [Ring R] (I : Ideal R) (X : Type u) [AddCommGroup X]
    [Module Rᵐᵒᵖ X] (x : X) (r : R) :
    balAuxL R I X x (Submodule.Quotient.mk r) = Submodule.Quotient.mk (op r • x) :=
  balFun_mk R I X x r

lemma balAuxL_zero (R : Type u) [Ring R] (I : Ideal R) (X : Type u) [AddCommGroup X]
    [Module Rᵐᵒᵖ X] : balAuxL R I X 0 = 0 := by
  refine LinearMap.ext ?_
  intro q
  obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective (p := (I : Submodule R R)) q
  rw [balAuxL_mk, LinearMap.zero_apply, smul_zero, Submodule.Quotient.mk_zero]

lemma balAuxL_add (R : Type u) [Ring R] (I : Ideal R) (X : Type u) [AddCommGroup X]
    [Module Rᵐᵒᵖ X] (x y : X) :
    balAuxL R I X (x + y) = balAuxL R I X x + balAuxL R I X y := by
  refine LinearMap.ext ?_
  intro q
  obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective (p := (I : Submodule R R)) q
  rw [balAuxL_mk, LinearMap.add_apply, balAuxL_mk, balAuxL_mk, smul_add,
    Submodule.Quotient.mk_add]

theorem balTensor_fwdMap (R : Type u) [Ring R] (I : Ideal R) (X : Type u) [AddCommGroup X]
    [Module Rᵐᵒᵖ X] :
    ∃ f : X →ₗ[ℤ] (R ⧸ I) →ₗ[ℤ] (X ⧸ Work.ORLyndon.balImage R I X),
      ∀ (x : X) (r : R),
        f x (Submodule.Quotient.mk r) = Submodule.Quotient.mk (MulOpposite.op r • x) := by
  refine ⟨AddMonoidHom.toIntLinearMap
    { toFun := fun x => balAuxL R I X x
      map_zero' := balAuxL_zero R I X
      map_add' := balAuxL_add R I X }, ?_⟩
  intro x r
  exact balAuxL_mk R I X x r

end Work.ORLyndon
