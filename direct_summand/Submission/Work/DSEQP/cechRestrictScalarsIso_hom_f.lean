import Mathlib
import Submission.Work.DSEQP.PerfChainAux

/-!
# The degree-`n` component of `cechRestrictScalarsIso`

`Work.DSEQP.cechRestrictScalarsIso` is the comparison
`restrictScalars ψ (cech F) ≅ cech (F ⋙ restrictScalars ψ)`, built as
`alternatingCofaceMapComplexMapHomologicalComplexIso R K ≪≫
  (alternatingCofaceMapComplex A).mapIso (whiskeringLeft _ (evalOpObjIso R F))`.

Its degree-`n` component is therefore `𝟙 _ ≫ (evalOpObjIso R F).hom.app (op (E _⦋n⦌))`:
the first half contributes the identity in each degree, while `evalOpObjIso` is
componentwise the canonical comparison of a product with the product of the images,
i.e. `piComparison R`.  Discarding the identity needs nothing more than
`Category.id_comp`, after which both sides are definitionally the same
`piComparison`.
-/

namespace Work.DSEQP

universe u u₁ u₂ v₁ v₂

open CategoryTheory AlgebraicGeometry Limits Opposite

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000

/-- The degree-`n` component of `alternatingCofaceMapComplexMapHomologicalComplexIso`
is the identity (its very definition is `isoOfComponents (fun _ => Iso.refl _)`). -/
theorem alternatingCofaceMapComplexMapHomologicalComplexIso_hom_f_eq_id
    {S : Type u₁} [Category.{v₁} S] [Preadditive S]
    {D : Type u₂} [Category.{v₂} D] [Preadditive D]
    (F : S ⥤ D) [F.Additive] (K : CosimplicialObject S) (n : ℕ) :
    (Work.DSF1.Sheaf.alternatingCofaceMapComplexMapHomologicalComplexIso F K).hom.f n =
      𝟙 _ :=
  rfl

theorem cechRestrictScalarsIso_hom_f {A W : Type u} [CommRing A] [CommRing W] (ψ : A →+* W)
    {X : AlgebraicGeometry.Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    (F : CategoryTheory.Functor (Opposite X.Opens) (ModuleCat.{u} W)) (n : ℕ) :
    (Work.DSEQP.cechRestrictScalarsIso ψ U F).hom.f n =
      CategoryTheory.Limits.piComparison (ModuleCat.restrictScalars ψ)
        (fun a : ((CategoryTheory.Limits.FormalCoproduct.mk ι U).cech.obj
            (Opposite.op (SimplexCategory.mk n))).I =>
          F.obj (Opposite.op (((CategoryTheory.Limits.FormalCoproduct.mk ι U).cech.obj
            (Opposite.op (SimplexCategory.mk n))).obj a))) := by
  dsimp only [Work.DSEQP.cechRestrictScalarsIso]
  rw [CategoryTheory.Iso.trans_hom, HomologicalComplex.comp_f]
  rw [alternatingCofaceMapComplexMapHomologicalComplexIso_hom_f_eq_id]
  -- the composite of the identity with the second half is the second half; the goal is
  -- only type-correct up to semireducible unfolding, so `erw` is used for this step,
  -- after which both sides are definitionally the `piComparison` of `evalOpObjIso`.
  erw [CategoryTheory.Category.id_comp]
  rfl

end Work.DSEQP
