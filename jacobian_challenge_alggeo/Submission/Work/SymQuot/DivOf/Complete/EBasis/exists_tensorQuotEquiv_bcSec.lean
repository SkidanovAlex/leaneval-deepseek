/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Base change of a quotient of the affine sections along the tower `C_L ⟶ C_F`

For a tower of field extensions `K → F → L`, an affine open `V ⊆ C` and an ideal
`I ⊆ Γ(C_F, V_F)`, the quotient `Γ(C_F, V_F) ⧸ I` base changes to
`Γ(C_L, V_L) ⧸ I·Γ(C_L, V_L)`:

`L ⊗[F] (Γ(C_F,V_F) ⧸ I) ≃ₐ[L] Γ(C_L,V_L) ⧸ I.map (bcSec F L V)`,

sending `1 ⊗ (b mod I)` to `(bcSec F L V b) mod I·Γ(C_L,V_L)`.

The mathematical content is (a) the affine description of the sections of the base change
(`sectionsLift` for the tower square `bcSquareTower`, which exhibits `Γ(C_L, V_L)` as
`L ⊗[F] Γ(C_F, V_F)`, compatible with `bcSec`), and (b) the standard right exactness of the
tensor product (`Algebra.TensorProduct.tensorQuotientEquiv` and `Ideal.quotientEquivAlg`).
-/
import Mathlib
import Submission.Work.SymQuot.DivOf.Complete.RhoData
import Submission.Work.SymQuot.DivOf.C1Defs
import Submission.Work.CurveBasics.Curve.BCSquare.SectionsTensor
import Submission.Work.SymQuot.DivOf.exists_eq_sum_secAlpha

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Work.SymQuot.DivOf.Complete.EBasis

open Work.CurveBasics

/-! ## Restriction of sections along an inequality (resp. an equality) of opens -/

/-- The restriction map induced by an inclusion of opens commutes with the structure map of a
curve: for a curve `C` over a field `K`, an inclusion `V' ⊆ U` of opens and `c : K`, the
restriction of the constant section `c` over `U` is the constant section `c` over `V'`. -/
lemma restrict_algebraMap {K : Type u} [Field K] {C : Curve K}
    (U V' : C.left.Opens) (h : V' ≤ U) (c : K) :
    (C.left.presheaf.map (homOfLE h).op).hom (algebraMap K Γ(C.left, U) c)
      = algebraMap K Γ(C.left, V') c := by
  show (C.left.presheaf.map (homOfLE h).op).hom
      ((C.hom.appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c))
    = (C.hom.appLE ⊤ V' le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c)
  have h1 : C.hom.appLE ⊤ U le_top ≫ C.left.presheaf.map (homOfLE h).op
      = C.hom.appLE ⊤ V' le_top := by
    rw [Scheme.Hom.appLE_map]
  rw [← h1, CommRingCat.comp_apply]

/-- Restriction of sections along an equality of opens is bijective (it is the map underlying an
isomorphism of `CommRingCat`, since the inclusion morphism of an equality is an isomorphism). -/
lemma restrict_bijective {K : Type u} [Field K] {C : Curve K} {U V' : C.left.Opens}
    (h : U = V') :
    Function.Bijective (C.left.presheaf.map (homOfLE (le_of_eq h.symm)).op).hom := by
  haveI : IsIso (homOfLE (le_of_eq h.symm)) := CategoryTheory.homOfLE_isIso_of_eq _ h.symm
  exact ConcreteCategory.bijective_of_isIso _

/-! ## The affine description of the sections of the base change -/

/-- **The sections of `C_L` over `V_L` are the base change of the sections of `C_F` over `V_F`.**
For an affine open `V ⊆ C` there is an isomorphism of `L`-algebras
`L ⊗[F] Γ(C_F, V_F) ≃ₐ[L] Γ(C_L, V_L)` sending `1 ⊗ a` to the pullback `bcSec F L V a` of the
section `a` along the tower morphism `C_L ⟶ C_F`. -/
theorem exists_algEquiv_tensor_bcSec {K : Type u} [Field K] {C : Curve K}
    {F : Type u} [Field F] [Algebra K F] {L : Type u} [Field L] [Algebra K L] [Algebra F L]
    [IsScalarTower K F L] {V : C.left.Opens} (hV : IsAffineOpen V) :
    ∃ E : TensorProduct F L
        ((C.baseChange F).left.presheaf.obj (Opposite.op (C.bcOpens F V)))
        ≃ₐ[L] ((C.baseChange L).left.presheaf.obj (Opposite.op (C.bcOpens L V))),
      ∀ a : (C.baseChange F).left.presheaf.obj (Opposite.op (C.bcOpens F V)),
        E (1 ⊗ₜ[F] a) = bcSec F L V a := by
  have hW : IsAffineOpen (C.bcOpens F V) :=
    Work.CurveBasics.BaseChange.isAffineOpen_bcOpens F V hV
  have hUV : (Work.SymQuot.DivOf.bcSquareTower (C := C) F L).π ⁻¹ᵁ (C.bcOpens F V)
      = C.bcOpens L V :=
    Work.SymQuot.DivOf.towerHom_preimage_bcOpens F L V
  have hSLbij : Function.Bijective (Curve.BCSquare.sectionsLift
      (Work.SymQuot.DivOf.bcSquareTower (C := C) F L) (C.bcOpens F V) hW) :=
    ⟨Curve.BCSquare.sectionsLift_injective _ _ _,
      Work.SymQuot.DivOf.sectionsLift_surjective_of_isAffineOpen _ _ _⟩
  let SL : TensorProduct F ((C.baseChange F).left.presheaf.obj (Opposite.op (C.bcOpens F V))) L →+*
      ((C.baseChange L).left.presheaf.obj
        (Opposite.op ((Work.SymQuot.DivOf.bcSquareTower (C := C) F L).π ⁻¹ᵁ (C.bcOpens F V)))) :=
    Curve.BCSquare.sectionsLift (Work.SymQuot.DivOf.bcSquareTower (C := C) F L)
      (C.bcOpens F V) hW
  let τ : ((C.baseChange L).left.presheaf.obj
        (Opposite.op ((Work.SymQuot.DivOf.bcSquareTower (C := C) F L).π ⁻¹ᵁ (C.bcOpens F V)))) →+*
      ((C.baseChange L).left.presheaf.obj (Opposite.op (C.bcOpens L V))) :=
    ((C.baseChange L).left.presheaf.map (homOfLE (le_of_eq hUV.symm)).op).hom
  let g : TensorProduct F L
      ((C.baseChange F).left.presheaf.obj (Opposite.op (C.bcOpens F V))) →+*
      ((C.baseChange L).left.presheaf.obj (Opposite.op (C.bcOpens L V))) :=
    τ.comp (SL.comp ((Algebra.TensorProduct.comm F
      ((C.baseChange F).left.presheaf.obj (Opposite.op (C.bcOpens F V))) L).symm :
        TensorProduct F L ((C.baseChange F).left.presheaf.obj (Opposite.op (C.bcOpens F V))) →+*
          TensorProduct F ((C.baseChange F).left.presheaf.obj (Opposite.op (C.bcOpens F V))) L))
  have hτbij : Function.Bijective τ := by
    rw [show τ = (fun x => ((C.baseChange L).left.presheaf.map
        (homOfLE (le_of_eq hUV.symm)).op).hom x) from rfl]
    exact restrict_bijective (C := C.baseChange L) hUV
  have hgSL : ∀ a : (C.baseChange F).left.presheaf.obj (Opposite.op (C.bcOpens F V)),
      g (1 ⊗ₜ[F] a) = bcSec F L V a := by
    intro a
    have h1 : (Algebra.TensorProduct.comm F
        ((C.baseChange F).left.presheaf.obj (Opposite.op (C.bcOpens F V))) L).symm
          (1 ⊗ₜ[F] a)
        = a ⊗ₜ[F] (1 : L) := by
      rw [Algebra.TensorProduct.comm_symm_tmul]
    have h2 : SL (a ⊗ₜ[F] (1 : L)) =
        (Work.SymQuot.DivOf.BCSquareBaseChange.towerHom (C := C) (F := F) (F' := L)).app
          (C.bcOpens F V) a :=
      Curve.BCSquare.sectionsLift_tmul_one _ _ _ a
    have h3 : bcSec F L V a = τ ((Work.SymQuot.DivOf.BCSquareBaseChange.towerHom
        (C := C) (F := F) (F' := L)).app (C.bcOpens F V) a) := rfl
    show τ (SL ((Algebra.TensorProduct.comm F
      ((C.baseChange F).left.presheaf.obj (Opposite.op (C.bcOpens F V))) L).symm
        (1 ⊗ₜ[F] a))) = bcSec F L V a
    rw [h1, h2, h3]
  have hgcomm : ∀ l : L, g (algebraMap L (TensorProduct F L
      ((C.baseChange F).left.presheaf.obj (Opposite.op (C.bcOpens F V)))) l)
      = algebraMap L ((C.baseChange L).left.presheaf.obj (Opposite.op (C.bcOpens L V))) l := by
    intro l
    have h1 : algebraMap L (TensorProduct F L
        ((C.baseChange F).left.presheaf.obj (Opposite.op (C.bcOpens F V)))) l
        = l ⊗ₜ[F] (1 : (C.baseChange F).left.presheaf.obj (Opposite.op (C.bcOpens F V))) := by
      rw [Algebra.TensorProduct.algebraMap_apply (R := F) (S := L) (A := L)
        (B := (C.baseChange F).left.presheaf.obj (Opposite.op (C.bcOpens F V)))]
      simp
    have h2 : (Algebra.TensorProduct.comm F
        ((C.baseChange F).left.presheaf.obj (Opposite.op (C.bcOpens F V))) L).symm
          (l ⊗ₜ[F] (1 : (C.baseChange F).left.presheaf.obj (Opposite.op (C.bcOpens F V))))
        = (1 : (C.baseChange F).left.presheaf.obj (Opposite.op (C.bcOpens F V))) ⊗ₜ[F] l := by
      rw [Algebra.TensorProduct.comm_symm_tmul]
    have h3 : SL ((1 : (C.baseChange F).left.presheaf.obj (Opposite.op (C.bcOpens F V)))
          ⊗ₜ[F] l)
        = algebraMap L ((C.baseChange L).left.presheaf.obj
            (Opposite.op ((Work.SymQuot.DivOf.bcSquareTower (C := C) F L).π ⁻¹ᵁ
              (C.bcOpens F V)))) l :=
      Curve.BCSquare.sectionsLift_one_tmul _ _ _ l
    have h4 : τ (algebraMap L ((C.baseChange L).left.presheaf.obj
          (Opposite.op ((Work.SymQuot.DivOf.bcSquareTower (C := C) F L).π ⁻¹ᵁ
            (C.bcOpens F V)))) l)
        = algebraMap L ((C.baseChange L).left.presheaf.obj (Opposite.op (C.bcOpens L V))) l := by
      rw [show τ = (fun x => ((C.baseChange L).left.presheaf.map
          (homOfLE (le_of_eq hUV.symm)).op).hom x) from rfl]
      exact restrict_algebraMap (C := C.baseChange L) _ _ (le_of_eq hUV.symm) l
    show τ (SL ((Algebra.TensorProduct.comm F
      ((C.baseChange F).left.presheaf.obj (Opposite.op (C.bcOpens F V))) L).symm
        (algebraMap L (TensorProduct F L
          ((C.baseChange F).left.presheaf.obj (Opposite.op (C.bcOpens F V)))) l)))
      = algebraMap L ((C.baseChange L).left.presheaf.obj (Opposite.op (C.bcOpens L V))) l
    rw [h1, h2, h3, h4]
  have hgbij : Function.Bijective g := by
    have hflip : Function.Bijective ((Algebra.TensorProduct.comm F
        ((C.baseChange F).left.presheaf.obj (Opposite.op (C.bcOpens F V))) L).symm :
          TensorProduct F L
            ((C.baseChange F).left.presheaf.obj (Opposite.op (C.bcOpens F V))) →+*
          TensorProduct F ((C.baseChange F).left.presheaf.obj (Opposite.op (C.bcOpens F V))) L) :=
      (Algebra.TensorProduct.comm F
        ((C.baseChange F).left.presheaf.obj (Opposite.op (C.bcOpens F V))) L).symm.bijective
    exact hτbij.comp (hSLbij.comp hflip)
  refine ⟨AlgEquiv.ofBijective (AlgHom.mk g hgcomm) hgbij, fun a => ?_⟩
  rw [AlgEquiv.ofBijective_apply]
  exact hgSL a

/-! ## The quotient of a base change -/

/-- **Right exactness of the tensor product, in the form needed here.**  Let `A` be an `F`-algebra
and `B` an `L`-algebra which is the base change of `A` along `L/F`, witnessed by an isomorphism
`e : L ⊗[F] A ≃ₐ[L] B` with `e (1 ⊗ a) = φ a` for a ring hom `φ : A →+* B`.  Then for every ideal
`I ⊆ A` the base change of `A ⧸ I` to `L` is the quotient of `B` by the extension ideal
`I.map φ`, and the isomorphism is the canonical one sending `1 ⊗ (b mod I)` to `φ b mod I.map φ`.

Concretely, `L ⊗[F] (A ⧸ I)` is `(L ⊗[F] A) ⧸ I·(L ⊗[F] A)` (`tensorQuotientEquiv`), and `e`
identifies the ideal `I·(L ⊗[F] A)` with `I.map φ` (`Ideal.quotientEquivAlg`). -/
theorem exists_tensorQuotEquiv_of_algEquiv {F L : Type u} [Field F] [Field L] [Algebra F L]
    {A : Type u} [CommRing A] [Algebra F A] {B : Type u} [CommRing B] [Algebra L B]
    (φ : A →+* B) (e : TensorProduct F L A ≃ₐ[L] B) (he : ∀ a, e (1 ⊗ₜ[F] a) = φ a)
    (I : Ideal A) :
    ∃ E : TensorProduct F L (A ⧸ I) ≃ₐ[L] B ⧸ I.map φ,
      ∀ b : A, E (1 ⊗ₜ[F] Ideal.Quotient.mk I b) = Ideal.Quotient.mk (I.map φ) (φ b) := by
  have hkey : I.map φ =
      (I.map (Algebra.TensorProduct.includeRight (R := F) (A := L) (B := A))).map
        (e : TensorProduct F L A →+* B) := by
    rw [show (I.map (Algebra.TensorProduct.includeRight (R := F) (A := L) (B := A))).map
        (e : TensorProduct F L A →+* B)
        = I.map ((e : TensorProduct F L A →+* B).comp
            (Algebra.TensorProduct.includeRight (R := F) (A := L) (B := A))) from
      Ideal.map_map _ _]
    congr 1
    ext a
    simp [RingHom.comp_apply, Algebra.TensorProduct.includeRight_apply, he]
  refine ⟨(Algebra.TensorProduct.tensorQuotientEquiv (R := F) L A L I).trans
    (Ideal.quotientEquivAlg (I.map _) (I.map φ) e hkey), ?_⟩
  intro b
  simp [AlgEquiv.trans_apply, Ideal.quotientEquivAlg_mk, he]

/-! ## The target -/

theorem exists_tensorQuotEquiv_bcSec {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {F : Type u} [Field F] [Algebra K F] {L : Type u} [Field L] [Algebra K L] [Algebra F L]
    [IsScalarTower K F L] {V : C.left.Opens} [Nonempty V]
    (hV : AlgebraicGeometry.IsAffineOpen V)
    (I : Ideal ((C.baseChange F).left.presheaf.obj (Opposite.op (C.bcOpens F V)))) :
    ∃ e : TensorProduct F L ((C.baseChange F).left.presheaf.obj (Opposite.op (C.bcOpens F V)) ⧸ I)
        ≃ₐ[L] ((C.baseChange L).left.presheaf.obj (Opposite.op (C.bcOpens L V)) ⧸
          I.map (Work.SymQuot.DivOf.bcSec F L V)),
      ∀ b : (C.baseChange F).left.presheaf.obj (Opposite.op (C.bcOpens F V)),
        e ((1 : L) ⊗ₜ[F] Ideal.Quotient.mk I b) =
          Ideal.Quotient.mk (I.map (Work.SymQuot.DivOf.bcSec F L V))
            (Work.SymQuot.DivOf.bcSec F L V b) := by
  obtain ⟨E, hE⟩ := exists_algEquiv_tensor_bcSec (C := C) (F := F) (L := L) hV
  exact exists_tensorQuotEquiv_of_algEquiv (Work.SymQuot.DivOf.bcSec F L V) E hE I

end Work.SymQuot.DivOf.Complete.EBasis
