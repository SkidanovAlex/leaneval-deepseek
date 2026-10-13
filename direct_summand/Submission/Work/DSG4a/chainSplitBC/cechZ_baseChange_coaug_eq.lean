import Mathlib
import Submission.Work.DSG4a.CSB_Defs
import Submission.Work.DSG4a.Data

/-!
# `cechZ_baseChange_coaug_eq`

The Čech coaugmentation is *unique* (`Work.DSG4a.coaug_eq_of_coaugClause`): a chain map
`A[0] ⟶ cechZ A X f U` whose degree-`0` component is the Čech coaugmentation is determined by
that component.  This file exploits the uniqueness to identify the base-changed coaugmentation
`ccAn'` of `cechZ A' X_{A'} f' U'` with the image of `ccAn` under the base change comparison:

`ccAn' = eS ≫ (baseChangeComplexFunctor).map ccAn ≫ Φ`.

The hypotheses say precisely that `Φ` carries the class of `coaugZElem A X f U` to the class of
`coaugZElem A' X' f' U'` (`hΦ`), so the composite is a chain map with the same degree-`0`
component as `ccAn'`; uniqueness finishes.

The proof is elementwise: a morphism `(singleZ A).X 0 ⟶ M` is determined by its value at the
canonical generator `(singleSelf A).inv 1` (the `singleSelf A` isomorphism
`(singleZ A).X 0 ≅ A`), because it is `A`-linear and the source is free of rank one.
-/

namespace Work.DSG4a.chainSplitBC

open CategoryTheory AlgebraicGeometry Limits
open scoped ChangeOfRings TensorProduct

set_option backward.isDefEq.respectTransparency false
universe u

/-- A morphism out of the degree-`0` term of the single-object complex `A[0]` is determined by
its value at the canonical generator `(singleSelf A).inv 1`. -/
lemma csbc_singleZ_hom_ext {A : Type u} [CommRing A] {M : ModuleCat.{u} A}
    {p q : (Work.DSG4a.singleZ A).X 0 ⟶ M}
    (h : ConcreteCategory.hom p ((ConcreteCategory.hom (Work.DSG4a.singleSelf A).inv) 1) =
         ConcreteCategory.hom q ((ConcreteCategory.hom (Work.DSG4a.singleSelf A).inv) 1)) :
    p = q := by
  have hp : p = (Work.DSG4a.singleSelf A).hom ≫ ((Work.DSG4a.singleSelf A).inv ≫ p) := by
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have hq : q = (Work.DSG4a.singleSelf A).hom ≫ ((Work.DSG4a.singleSelf A).inv ≫ q) := by
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have hpq : (Work.DSG4a.singleSelf A).inv ≫ p = (Work.DSG4a.singleSelf A).inv ≫ q := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp]
    exact h
  rw [hp, hq, hpq]

/-- The identification of the degree-`0` term of `cechZ` with the degree-`0` term of `cech`
sends `coaugZElem` to the Čech coaugmentation applied to `1`. -/
lemma csbc_coaugZElem_extendXIso_hom {A : Type u} [CommRing A] {X : Scheme.{u}}
    {f : X ⟶ Spec (.of A)} {ι : Type u} {U : ι → X.Opens} :
    ConcreteCategory.hom ((DSMap.cech A X f U).extendXIso ComplexShape.embeddingUpNat
        (i := 0) rfl).hom
        (Work.DSG4a.coaugZElem A X f U) =
      ConcreteCategory.hom (DSMap.coaug0 A X f U) 1 := by
  show ConcreteCategory.hom ((DSMap.cech A X f U).extendXIso ComplexShape.embeddingUpNat
        (i := 0) rfl).hom
        ((DSMap.coaug0 A X f U ≫
          ((DSMap.cech A X f U).extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).inv) 1) =
      ConcreteCategory.hom (DSMap.coaug0 A X f U) 1
  rw [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]

/-- The elementwise form of `Work.DSG4a.coaugClause`: the degree-`0` component sends the
canonical generator of `A[0]` to `coaugZElem`. -/
lemma csbc_coaugClause_coaugElem {A : Type u} [CommRing A] {X : Scheme.{u}}
    {f : X ⟶ Spec (.of A)} {ι : Type u} {U : ι → X.Opens}
    {γ : Work.DSG4a.singleZ A ⟶ DSMap.cechZ A X f U} (h : Work.DSG4a.coaugClause X f U γ) :
    ConcreteCategory.hom (γ.f 0) ((ConcreteCategory.hom (Work.DSG4a.singleSelf A).inv) 1) =
      Work.DSG4a.coaugZElem A X f U := by
  have hm : γ.f 0 ≫ ((DSMap.cech A X f U).extendXIso ComplexShape.embeddingUpNat
        (i := 0) rfl).hom =
      (Work.DSG4a.singleSelf A).hom ≫ DSMap.coaug0 A X f U := h
  have h2 := congrArg (fun (k : (Work.DSG4a.singleZ A).X 0 ⟶ (DSMap.cech A X f U).X 0) =>
      ConcreteCategory.hom k ((ConcreteCategory.hom (Work.DSG4a.singleSelf A).inv) 1)) hm
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h2
  rw [Iso.inv_hom_id_apply] at h2
  rw [← csbc_coaugZElem_extendXIso_hom (A := A) (X := X) (f := f) (U := U)] at h2
  exact (ConcreteCategory.bijective_of_isIso ((DSMap.cech A X f U).extendXIso
    ComplexShape.embeddingUpNat (i := 0) rfl).hom).1 h2

/-- **The degree-`0` computation.**  The composite `eS ≫ (baseChangeComplexFunctor).map ccAn ≫ Φ`
sends the canonical generator of `A'[0]` to `coaugZElem A' X' f' U'`, using the uniqueness
clause of `ccAn` and the compatibility hypothesis `hΦ` on `Φ` (at `a' = 1`). -/
lemma csbc_eS_map_coaugZ_apply {A : Type u} [CommRing A] {A' : Type u} [CommRing A']
    [Algebra A A'] {X : Scheme.{u}} {f : X ⟶ Spec (.of A)} {ι : Type u} {U : ι → X.Opens}
    (ccAn : Work.DSG4a.singleZ A ⟶ DSMap.cechZ A X f U)
    (hccAn : Work.DSG4a.coaugClause X f U ccAn)
    (Φ : Work.DSG4a.baseChangeComplex (A := A) (A' := A') (DSMap.cechZ A X f U) ⟶
      DSMap.cechZ A' (Work.DSG4a.baseChangeScheme X f) (Work.DSG4a.baseChangeSnd X f)
        (fun i => Work.DSG4a.baseChangeOpen X f (U i)))
    (hΦ : ∀ a' : A', (Φ.f 0) (a' ⊗ₜ[A, algebraMap A A'] Work.DSG4a.coaugZElem A X f U) =
      a' • Work.DSG4a.coaugZElem A' (Work.DSG4a.baseChangeScheme X f)
        (Work.DSG4a.baseChangeSnd X f) (fun i => Work.DSG4a.baseChangeOpen X f (U i))) :
    ConcreteCategory.hom
        ((Work.DSG4a.eS A A' ≫
          (Work.DSG4a.baseChangeComplexFunctor (A := A) (A' := A')).map ccAn ≫ Φ).f 0)
        ((ConcreteCategory.hom (Work.DSG4a.singleSelf A').inv) 1) =
      Work.DSG4a.coaugZElem A' (Work.DSG4a.baseChangeScheme X f)
        (Work.DSG4a.baseChangeSnd X f) (fun i => Work.DSG4a.baseChangeOpen X f (U i)) := by
  have hstep1 : ConcreteCategory.hom
        (((Work.DSG4a.baseChangeComplexFunctor (A := A) (A' := A')).map ccAn).f 0)
        (Work.DSG4a.eSElem A A') =
      Work.DSG4a.oneTmul (A := A) (A' := A')
        (ConcreteCategory.hom (ccAn.f 0)
          ((ConcreteCategory.hom (Work.DSG4a.singleSelf A).inv) 1)) := by
    rw [Work.DSG4a.baseChangeComplexFunctor_map_f (A := A) (A' := A') ccAn 0]
    exact Work.DSG4a.extendScalars_map_one_tmul (A := A) (A' := A') (ccAn.f 0)
      ((ConcreteCategory.hom (Work.DSG4a.singleSelf A).inv) 1)
  rw [show ((Work.DSG4a.eS A A' ≫
        (Work.DSG4a.baseChangeComplexFunctor (A := A) (A' := A')).map ccAn ≫ Φ).f 0)
      = ((Work.DSG4a.eS A A').f 0 ≫
          ((Work.DSG4a.baseChangeComplexFunctor (A := A) (A' := A')).map ccAn).f 0) ≫
          Φ.f 0 from rfl]
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  rw [show ConcreteCategory.hom ((Work.DSG4a.eS A A').f 0)
        ((ConcreteCategory.hom (Work.DSG4a.singleSelf A').inv) 1) =
        Work.DSG4a.eSElem A A' from Work.DSG4a.eS_f_zero_apply_inv_one A A']
  rw [hstep1]
  rw [show ConcreteCategory.hom (ccAn.f 0)
        ((ConcreteCategory.hom (Work.DSG4a.singleSelf A).inv) 1) =
        Work.DSG4a.coaugZElem A X f U from csbc_coaugClause_coaugElem hccAn]
  rw [show Work.DSG4a.oneTmul (A := A) (A' := A') (Work.DSG4a.coaugZElem A X f U) =
        (1 : A') ⊗ₜ[A, algebraMap A A'] Work.DSG4a.coaugZElem A X f U from rfl]
  rw [hΦ 1]
  rw [one_smul]

theorem cechZ_baseChange_coaug_eq {A : Type u} [CommRing A] {A' : Type u} [CommRing A']
    [Algebra A A'] {X : AlgebraicGeometry.Scheme.{u}}
    {f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)} {ι : Type u} {U : ι → X.Opens}
    (ccAn : Work.DSG4a.singleZ A ⟶ DSMap.cechZ A X f U)
    (hccAn : Work.DSG4a.coaugClause X f U ccAn)
    (ccAn' : Work.DSG4a.singleZ A' ⟶ DSMap.cechZ A' (Work.DSG4a.baseChangeScheme X f)
      (Work.DSG4a.baseChangeSnd X f) (fun i => Work.DSG4a.baseChangeOpen X f (U i)))
    (hccAn' : Work.DSG4a.coaugClause (Work.DSG4a.baseChangeScheme X f)
      (Work.DSG4a.baseChangeSnd X f) (fun i => Work.DSG4a.baseChangeOpen X f (U i)) ccAn')
    (Φ : Work.DSG4a.baseChangeComplex (A := A) (A' := A') (DSMap.cechZ A X f U) ⟶
      DSMap.cechZ A' (Work.DSG4a.baseChangeScheme X f) (Work.DSG4a.baseChangeSnd X f)
        (fun i => Work.DSG4a.baseChangeOpen X f (U i)))
    (hΦ : ∀ a' : A', (Φ.f 0) (a' ⊗ₜ[A, algebraMap A A'] Work.DSG4a.coaugZElem A X f U) =
      a' • Work.DSG4a.coaugZElem A' (Work.DSG4a.baseChangeScheme X f)
        (Work.DSG4a.baseChangeSnd X f) (fun i => Work.DSG4a.baseChangeOpen X f (U i))) :
    ccAn' = Work.DSG4a.eS A A' ≫
      (Work.DSG4a.baseChangeComplexFunctor (A := A) (A' := A')).map ccAn ≫ Φ := by
  apply Work.DSG4a.coaug_eq_of_coaugClause hccAn'
  apply csbc_singleZ_hom_ext
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  rw [Iso.inv_hom_id_apply]
  rw [csbc_eS_map_coaugZ_apply ccAn hccAn Φ hΦ]
  exact csbc_coaugZElem_extendXIso_hom (A := A') (X := Work.DSG4a.baseChangeScheme X f)
    (f := Work.DSG4a.baseChangeSnd X f) (U := fun i => Work.DSG4a.baseChangeOpen X f (U i))

end Work.DSG4a.chainSplitBC
