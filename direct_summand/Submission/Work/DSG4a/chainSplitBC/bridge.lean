import Mathlib
import Submission.Work.DSG4a.CSB_Defs

/-!
# DSG4a / `chainSplit_ccBase_iff`: the flavour bridge

The base change of a complex of `A`-modules along an algebra `A → A'` is
`baseChangeComplex P = (extendScalars (algebraMap A A')).mapHomologicalComplex P`, whose
degree-`i` term is the `ModuleCat A'`-object
`(ModuleCat.extendScalars (algebraMap A A')).obj (P.X i)`.  Its carrier is the "compHom"
tensor product `↥((restrictScalars (algebraMap A A')).obj (ModuleCat.of A' A')) ⊗[A] ↥(P.X i)`,
i.e. the tensor product in which the `A`-module structure on the left factor `A'` is the
*restricted* one (`Module.compHom`), while the `A'`-module structure is multiplication.

The *same* object is, mathematically, the "algebra" tensor product `A' ⊗[A] ↥(P.X i)`, in which
the `A`-module structure on `A'` is the one induced by the `Algebra` instance.  The two are not
definitionally equal (the `A`-module structures are different terms), and this file provides the
missing isomorphism

`extTensorEquiv : ↥((extendScalars (algebraMap A A')).obj M) ≃ₗ[A'] (A' ⊗[A] ↥M)`,

which is the identity on the underlying sets, together with its values on pure tensors.  It is
built as the heterobasic `TensorProduct.congr` of the identity `A`-linear (hence `A'`-linear)
equivalence `↥((restrictScalars f).obj (of A' A')) ≃ₗ[A] A'` with the identity of `↥M`; the
`A'`-linearity on pure tensors is `ModuleCat.ExtendScalars.smul_tmul` on one side and
`TensorProduct.smul_tmul'` on the other.

Everything in this file is used by `chainSplit_ccBase_iff`.
-/

namespace Work.DSG4a.chainSplitBC

open CategoryTheory AlgebraicGeometry Limits
open scoped ChangeOfRings TensorProduct
open TensorProduct

set_option backward.isDefEq.respectTransparency false
universe u

variable {A : Type u} [CommRing A] {A' : Type u} [CommRing A'] [Algebra A A']

/-- **The flavour bridge.** The two realizations of the extension of scalars `A' ⊗[A] M` -- the
`ModuleCat`-one appearing as a term of `baseChangeComplex` and the algebra one -- are canonically
`A'`-linearly isomorphic by the identity on the underlying sets. -/
noncomputable def extTensorEquiv (M : ModuleCat.{u} A) :
    ↥((ModuleCat.extendScalars (algebraMap A A')).obj M) ≃ₗ[A'] (A' ⊗[A] ↥M) := by
  let eN : ↥((ModuleCat.restrictScalars (algebraMap A A')).obj (ModuleCat.of A' A')) ≃ₗ[A] A' :=
    { toFun := fun x => (x : A'), invFun := fun y => y,
      map_add' := fun x y => rfl,
      map_smul' := fun r x => by simp [Algebra.smul_def, ModuleCat.restrictScalars.smul_def],
      left_inv := fun x => rfl, right_inv := fun y => rfl }
  let e : ↥((ModuleCat.restrictScalars (algebraMap A A')).obj (ModuleCat.of A' A')) ⊗[A] ↥M ≃ₗ[A]
      (A' ⊗[A] ↥M) := TensorProduct.congr eN (LinearEquiv.refl A ↥M)
  have hσ : ∀ (a : A') (z : ↥((ModuleCat.extendScalars (algebraMap A A')).obj M)),
      e (a • z) = a • e z := by
    intro a z
    induction z using TensorProduct.inductionOn with
    | tmul n m =>
      show e (a • (n ⊗ₜ[A] m)) = a • e (n ⊗ₜ[A] m)
      dsimp only [e]
      rw [TensorProduct.congr_tmul]
      rw [TensorProduct.smul_tmul', TensorProduct.congr_tmul, TensorProduct.smul_tmul']
      congr 1 <;> dsimp only [eN] <;> rfl
    | add z₁ z₂ h₁ h₂ => simp only [smul_add, map_add, h₁, h₂]
  exact
  { toFun := ⇑e
    invFun := ⇑e.symm
    map_add' := fun x y => e.map_add x y
    map_smul' := hσ
    left_inv := fun x => e.left_inv x
    right_inv := fun y => e.right_inv y }

/-- The flavour bridge is the identity on pure tensors. -/
theorem extTensorEquiv_tmul (M : ModuleCat.{u} A) (a : A') (m : ↥M) :
    extTensorEquiv (A := A) (A' := A') M (a ⊗ₜ[A, algebraMap A A'] m) = a ⊗ₜ[A] m := by
  simp only [extTensorEquiv, TensorProduct.congr_tmul]
  rfl

/-- The inverse of the flavour bridge on pure tensors. -/
theorem extTensorEquiv_symm_tmul (M : ModuleCat.{u} A) (a : A') (m : ↥M) :
    (extTensorEquiv (A := A) (A' := A') M).symm (a ⊗ₜ[A] m) = a ⊗ₜ[A, algebraMap A A'] m := by
  rw [← extTensorEquiv_tmul (A := A) (A' := A') M a m, LinearEquiv.symm_apply_apply]

/-- The differential of a base-changed complex acts on a pure tensor by base-changing the
differential. -/
theorem baseChangeComplex_d_tmul (P : CochainComplex (ModuleCat.{u} A) ℤ) (a : A')
    (m : ↥(P.X (-1))) :
    ((Work.DSG4a.baseChangeComplex (A := A) (A' := A') P).d (-1) 0).hom
        (a ⊗ₜ[A, algebraMap A A'] m)
      = a ⊗ₜ[A, algebraMap A A'] ((P.d (-1) 0).hom m) := by
  rw [Work.DSG4a.baseChangeComplex_d]
  exact ModuleCat.ExtendScalars.map_tmul (algebraMap A A') (P.d (-1) 0) a m

end Work.DSG4a.chainSplitBC
