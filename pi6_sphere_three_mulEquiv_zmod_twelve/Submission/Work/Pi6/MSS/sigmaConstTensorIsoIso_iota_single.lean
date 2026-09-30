import Mathlib
import Submission.Work.SSSR.serreE1CoefExplicit
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The coefficient isomorphism `sigmaConstTensorIsoIso` on a single coproduct inclusion

For a commutative ring `R`, a module `M` and a type `S`, the isomorphism

`sigmaConstTensorIsoIso M : (∐_S R) ⊗ M ≅ ∐_S M`

of `Submission/Work/SSSR/serreE1CoefExplicit.lean` is the composite of the comparison
`sigmaConstObjCompIso (tensorRight M) R : (∐_S R) ⊗ M ≅ ∐_S (R ⊗ M)` and the coproduct
`sigmaConst.mapIso (λ_ M) : ∐_S (R ⊗ M) ≅ ∐_S M`.

This file records the behaviour of this isomorphism on a *single* coproduct inclusion
`ι_t : R ⟶ ∐_S R`: whiskering by `M` and applying the isomorphism is the same as first applying
the unit of the monoidal structure `λ_ M : R ⊗ M ≅ M` and then including at `t`,

`(ι_t ▷ M) ≫ (sigmaConstTensorIsoIso M).hom.app S = (λ_ M).hom ≫ ι_t`.

The two auxiliary lemmas `sigmaConstObjCompIso_hom_app_ι` and `sigmaConst_mapIso_ι` state this
for the two factors separately, in the generality in which the factors are defined.
-/

set_option linter.style.haveILetI false
set_option autoImplicit false

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped MonoidalCategory

/-- **The component of `sigmaConstObjCompIso` on a coproduct inclusion.**  For a functor `F`
preserving coproducts and an object `R` of the source, the coproduct comparison
`sigmaConstObjCompIso F R : (sigmaConst.obj R) ⋙ F ≅ sigmaConst.obj (F.obj R)` sends the `t`-th
inclusion of `sigmaConst.obj R` to the `t`-th inclusion of `sigmaConst.obj (F.obj R)`. -/
lemma sigmaConstObjCompIso_hom_app_ι {C : Type*} [Category* C] {D : Type*} [Category* D]
    [HasCoproducts.{0} C] [HasCoproducts.{0} D] (F : C ⥤ D)
    [∀ (S : Type), PreservesColimitsOfShape (Discrete S) F] (R : C) (S : Type) (t : S) :
    F.map (Sigma.ι (fun _ : S => R) t)
        ≫ (Work.SSSR.StemsB.SphRat.sigmaConstObjCompIso F R).hom.app S
      = Sigma.ι (fun _ : S => F.obj R) t := by
  have h2 : inv (sigmaComparison F (fun _ : S => R))
      = (PreservesCoproduct.iso F (fun _ : S => R)).hom := by
    refine IsIso.inv_eq_of_hom_inv_id ?_
    rw [← PreservesCoproduct.inv_hom, Iso.inv_hom_id]
  rw [show (Work.SSSR.StemsB.SphRat.sigmaConstObjCompIso F R).hom.app S
      = (PreservesCoproduct.iso F (fun _ : S => R)).hom from rfl, ← h2]
  exact map_ι_comp_inv_sigmaComparison F (fun _ : S => R) t

/-- **The component of `sigmaConst.mapIso` on a coproduct inclusion.**  For an isomorphism
`e : X ≅ Y`, the induced map `∐_S X ⟶ ∐_S Y` sends the `t`-th inclusion of `∐_S X` to `e` followed
by the `t`-th inclusion of `∐_S Y`. -/
lemma sigmaConst_mapIso_ι {C : Type*} [Category* C] [HasCoproducts.{0} C]
    {X Y : C} (e : X ≅ Y) (S : Type) (t : S) :
    Sigma.ι (fun _ : S => X) t ≫ (Limits.sigmaConst.mapIso e).hom.app S
      = e.hom ≫ Sigma.ι (fun _ : S => Y) t := by
  rw [show (Limits.sigmaConst.mapIso e).hom.app S
      = Limits.Sigma.map (fun _ : S => e.hom) from rfl]
  exact Sigma.ι_map (fun _ : S => e.hom) t

theorem sigmaConstTensorIsoIso_iota_single {R : Type} [CommRing R] (M : ModuleCat R) (S : Type) (t : S) :
    CategoryTheory.CategoryStruct.comp
        (CategoryTheory.MonoidalCategoryStruct.whiskerRight
          (CategoryTheory.Limits.Sigma.ι (fun _ : S => ModuleCat.of R R) t) M)
        ((Work.SSSR.sigmaConstTensorIsoIso M).hom.app S)
      = CategoryTheory.CategoryStruct.comp
        (CategoryTheory.MonoidalCategory.leftUnitor M).hom
        (CategoryTheory.Limits.Sigma.ι (fun _ : S => M) t) := by
  haveI : ∀ (T : Type), PreservesColimitsOfShape (Discrete T) (tensorRight M) :=
    fun _ => inferInstance
  rw [Work.SSSR.sigmaConstTensorIsoIso]
  simp only [Iso.trans_hom, NatTrans.comp_app]
  rw [← Category.assoc]
  have hw : whiskerRight (Sigma.ι (fun _ : S => ModuleCat.of R R) t) M
      = (tensorRight M).map (Sigma.ι (fun _ : S => ModuleCat.of R R) t) := rfl
  rw [hw, sigmaConstObjCompIso_hom_app_ι (tensorRight M) (ModuleCat.of R R) S t,
    sigmaConst_mapIso_ι (X := (tensorRight M).obj (ModuleCat.of R R)) (leftUnitor M) S t]

end Work.Pi6.MSS
