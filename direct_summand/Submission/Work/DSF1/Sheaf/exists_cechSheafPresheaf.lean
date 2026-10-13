import Mathlib
import Submission.Work.DSMap.Map
import Submission.Work.DSF1.Modules.pushforward_unit_sections
import Submission.Work.DSF1.Sheaf.CechSheaf
import Submission.Work.DSF1.Sheaf.Beta
import Submission.Work.DSF1.Sheaf.restr_refl
import Submission.Work.DSF1.Sheaf.restr_trans
import Submission.Work.DSF1.Sheaf.mapHomologicalComplex_extendUpNat
import Submission.Work.DSF1.Sheaf.gammaCechComplexFunctor
import Submission.Work.DSF1.Sheaf.gammaCechPresheaf

namespace Work.DSF1.Sheaf

universe u

open CategoryTheory AlgebraicGeometry Opposite Limits TopologicalSpace

/-- The Čech presheaf of the structure sheaf: `V ↦ (V.ι)_* 𝒪_V`, with restriction maps `restr`. -/
noncomputable def cechSheafPresheaf (X : Scheme.{u}) : (X.Opens)ᵒᵖ ⥤ X.Modules where
  obj W := Work.DSF1.secSheaf W.unop
  map {W W'} f := Work.DSF1.Sheaf.restr (leOfHom f.unop)
  map_id W := by
    simpa using restr_refl X W.unop
  map_comp {W W' W''} f g := by
    show Work.DSF1.Sheaf.restr (leOfHom (f ≫ g).unop) =
      Work.DSF1.Sheaf.restr (leOfHom f.unop) ≫ Work.DSF1.Sheaf.restr (leOfHom g.unop)
    rw [restr_trans]

theorem exists_cechSheafPresheaf (A : Type u) [CommRing A] (X : AlgebraicGeometry.Scheme.{u})
    (f : Quiver.Hom X (AlgebraicGeometry.Spec (CommRingCat.of A))) {ι : Type u}
    (U : ι → X.Opens) :
    ∃ P : CategoryTheory.Functor (Opposite (X.Opens)) X.Modules,
      (∀ V : X.Opens, P.obj (Opposite.op V) =
        (AlgebraicGeometry.Scheme.Modules.pushforward (AlgebraicGeometry.Scheme.Opens.ι V)).obj
          (SheafOfModules.unit (AlgebraicGeometry.Scheme.Opens.toScheme V).ringCatSheaf)) ∧
      Nonempty (CategoryTheory.Iso
        ((CategoryTheory.Functor.mapHomologicalComplex (DSMap.GammaA A X f)
            (ComplexShape.up ℤ)).obj
          (HomologicalComplex.extend ((CategoryTheory.cechComplexFunctor U).obj P)
            ComplexShape.embeddingUpNat))
        (DSMap.cechZ A X f U)) := by
  refine ⟨cechSheafPresheaf X, fun V => rfl, ?_⟩
  obtain ⟨eΓ⟩ := gammaCechPresheaf A X f (cechSheafPresheaf X) (fun V => rfl)
    (fun V V' h => HEq.refl _)
  obtain ⟨eExt⟩ := mapHomologicalComplex_extendUpNat (DSMap.GammaA A X f)
    ((cechComplexFunctor U).obj (cechSheafPresheaf X))
  obtain ⟨eCech⟩ := gammaCechComplexFunctor A X f U (cechSheafPresheaf X)
  exact ⟨eExt ≪≫ (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat A)).mapIso
    (eCech ≪≫ (cechComplexFunctor U).mapIso eΓ) ≪≫ Iso.refl _⟩

end Work.DSF1.Sheaf
