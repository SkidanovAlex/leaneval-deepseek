import Mathlib
import Submission.Work.DSG4a.Data
import Submission.Work.DSG4a.cechZ_baseChange
import Submission.Work.DSG4a.quasiIso_baseChangeComplexFunctor

/-!
# `chainSplit_baseChange_iff` — auxiliary constructions

The canonical comparison `eS : A'[0] ⟶ A' ⊗[A] A[0]` of the single-object complexes, and the
base change `ccBase cc = eS ≫ (baseChangeComplexFunctor).map cc` of a coaugmentation `cc`.
-/

open CategoryTheory AlgebraicGeometry Limits
open scoped ChangeOfRings TensorProduct


set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

namespace Work.DSG4a

universe u

variable {A : Type u} [CommRing A] {A' : Type u} [CommRing A'] [Algebra A A']

/-- The `singleObjXSelf` isomorphism of the single complex at `0`. -/
noncomputable abbrev singleSelf (A : Type u) [CommRing A] :
    ((HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj
      (ModuleCat.of A A)).X 0 ≅ ModuleCat.of A A :=
  HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A A)

/-- The element `1 ⊗ m` of the extension of scalars of `M` along `A ⟶ A'`. -/
noncomputable def oneTmul {M : ModuleCat.{u} A} (m : ↥M) :
    ↥((ModuleCat.extendScalars (algebraMap A A')).obj M) :=
  (1 : A') ⊗ₜ[A, algebraMap A A'] m

/-- The extension of scalars of a linear map on `1 ⊗ m`. -/
theorem extendScalars_map_one_tmul {M M' : ModuleCat.{u} A} (g : M ⟶ M') (m : ↥M) :
    (ModuleCat.extendScalars (algebraMap A A')).map g (oneTmul (A := A) (A' := A') m) =
      oneTmul (A := A) (A' := A') (g.hom m) :=
  ModuleCat.ExtendScalars.map_tmul (algebraMap A A') g (1 : A') m

/-- The element `1 ⊗ 1` of `A' ⊗[A] A`, the image of the unit under `eS` in degree `0`. -/
noncomputable def eSElem (A : Type u) [CommRing A] (A' : Type u) [CommRing A'] [Algebra A A'] :
    ↥((baseChangeComplex (A := A) (A' := A') (singleZ A)).X 0) :=
  oneTmul (A := A) (A' := A') ((singleSelf A).inv (1 : A))

/-- The differential of a base-changed complex is the base change of the differential. -/
theorem baseChangeComplex_d (A : Type u) [CommRing A] (A' : Type u) [CommRing A'] [Algebra A A']
    (K : CochainComplex (ModuleCat.{u} A) ℤ) (i j : ℤ) :
    (baseChangeComplex (A := A) (A' := A') K).d i j =
      (ModuleCat.extendScalars (algebraMap A A')).map (K.d i j) :=
  Functor.mapHomologicalComplex_obj_d _ _ _ i j

/-- The degree-`i` component of the base change of a morphism of complexes. -/
theorem baseChangeComplexFunctor_map_f (A : Type u) [CommRing A] (A' : Type u) [CommRing A']
    [Algebra A A'] {K L : CochainComplex (ModuleCat.{u} A) ℤ} (f : K ⟶ L) (i : ℤ) :
    ((baseChangeComplexFunctor (A := A) (A' := A')).map f).f i =
      (ModuleCat.extendScalars (algebraMap A A')).map (f.f i) :=
  Functor.mapHomologicalComplex_map_f _ _ f i

/-- **The canonical comparison of the single-object complexes**: the inclusion of `A'[0]` into
the base change of `A[0]`, sending the unit to `1 ⊗ 1`. -/
noncomputable def eS (A : Type u) [CommRing A] (A' : Type u) [CommRing A'] [Algebra A A'] :
    singleZ A' ⟶ baseChangeComplex (A := A) (A' := A') (singleZ A) :=
  HomologicalComplex.mkHomFromSingle (V := ModuleCat.{u} A') (c := ComplexShape.up ℤ) (j := 0)
    (K := baseChangeComplex (A := A) (A' := A') (singleZ A)) (A := ModuleCat.of A' A')
    (φ := (singleSelf A').hom ≫
      ModuleCat.ofHom (LinearMap.toSpanSingleton A' _ (eSElem A A')))
    (hφ := fun k hk => by
      obtain rfl : k = 1 := by
        rw [ComplexShape.up_Rel] at hk
        omega
      rw [baseChangeComplex_d, HomologicalComplex.single_obj_d, Functor.map_zero, comp_zero])

/-- The degree-`0` component of `eS` sends the canonical generator of `A'[0]` to `1 ⊗ 1`. -/
theorem eS_f_zero_apply_inv_one (A : Type u) [CommRing A] (A' : Type u) [CommRing A']
    [Algebra A A'] :
    (eS A A').f 0 ((singleSelf A').inv (1 : A')) = eSElem A A' := by
  rw [eS, HomologicalComplex.mkHomFromSingle_f]
  show (ConcreteCategory.hom (ModuleCat.ofHom
      (LinearMap.toSpanSingleton A' _ (eSElem A A'))))
      ((ConcreteCategory.hom (singleSelf A').hom) ((ConcreteCategory.hom (singleSelf A').inv)
        (1 : A'))) = eSElem A A'
  rw [Iso.inv_hom_id_apply]
  show (LinearMap.toSpanSingleton A' _ (eSElem A A')) (1 : A') = eSElem A A'
  rw [LinearMap.toSpanSingleton_apply_one]

/-- The coaugmentation element of `eS` is `1 ⊗ 1`. -/
theorem eS_coaugElem (A : Type u) [CommRing A] (A' : Type u) [CommRing A'] [Algebra A A'] :
    Criterion.coaugElem (baseChangeComplex (A := A) (A' := A') (singleZ A)) (eS A A') =
      eSElem A A' := by
  rw [Criterion.coaugElem, ModuleCat.hom_comp, LinearMap.comp_apply, eS_f_zero_apply_inv_one]

/-- The **base change of a coaugmentation**: the coaugmentation `A'[0] ⟶ K ⊗[A] A'` of the
base-changed complex induced by `cc : A[0] ⟶ K`. -/
noncomputable def ccBase (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (cc : singleZ A ⟶ P) : singleZ A' ⟶ baseChangeComplex (A := A) (A' := A') P :=
  eS A A' ≫ (baseChangeComplexFunctor (A := A) (A' := A')).map cc

/-- The coaugmentation element of the base-changed coaugmentation is the base change of the
coaugmentation element. -/
theorem coaugElem_ccBase (P : CochainComplex (ModuleCat.{u} A) ℤ) (cc : singleZ A ⟶ P) :
    (Criterion.coaugElem (baseChangeComplex (A := A) (A' := A') P) (ccBase P cc) :
      ↥((ModuleCat.extendScalars (algebraMap A A')).obj (P.X 0))) =
      oneTmul (A := A) (A' := A') (Criterion.coaugElem P cc) := by
  rw [Criterion.coaugElem, CategoryTheory.comp_apply]
  rw [show (ccBase P cc).f 0 =
      (eS A A').f 0 ≫ ((baseChangeComplexFunctor (A := A) (A' := A')).map cc).f 0 from rfl,
    CategoryTheory.comp_apply]
  rw [show (ConcreteCategory.hom ((eS A A').f 0))
      ((ConcreteCategory.hom (singleSelf A').inv) (1 : A')) =
      oneTmul (A := A) (A' := A') ((singleSelf A).inv (1 : A)) from
    eS_f_zero_apply_inv_one A A']
  have h2 : (cc.f 0).hom ((singleSelf A).inv (1 : A)) = Criterion.coaugElem P cc := rfl
  refine (ConcreteCategory.congr_hom
    (baseChangeComplexFunctor_map_f (A := A) (A' := A') cc 0)
    (oneTmul (A := A) (A' := A') ((singleSelf A).inv (1 : A)))).trans ?_
  refine (extendScalars_map_one_tmul (A := A) (A' := A') (cc.f 0)
    ((singleSelf A).inv (1 : A))).trans ?_
  exact congrArg (oneTmul (A := A) (A' := A')) h2

end Work.DSG4a
