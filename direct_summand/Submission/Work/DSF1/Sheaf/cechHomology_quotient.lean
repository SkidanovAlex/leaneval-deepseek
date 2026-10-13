import Mathlib
import Submission.Work.DSF1.Sheaf.AcycDefs
import Submission.Work.DSF1.Sheaf.SSEBasic
import Submission.Work.DSF1.Sheaf.SSECore
import Submission.Work.DSF1.Sheaf.exists_lift_of_sectionsMap_eq_zero
import Submission.Work.DSF1.Sheaf.isZero_homology_quotient_of_shortExact
import Submission.Work.DSF1.Sheaf.cechComplex_map_shortExact

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

namespace Work.DSF1.Sheaf

open CategoryTheory AlgebraicGeometry Opposite Limits

universe u v

/-- The categorical product of a family of opens of a scheme is their infimum. -/
lemma piObj_eq_iInf {X : Scheme.{u}} {ι : Type v} (f : ι → X.Opens) :
    (∏ᶜ f : X.Opens) = iInf f := by
  apply le_antisymm
  · exact le_iInf fun i => (Pi.π f i).down.down
  · exact (Pi.lift (fun i => homOfLE (iInf_le f i))).down.down

/-- `Pi.map` of a family of zero morphisms is zero. -/
lemma pi_map_zero {β : Type u} {G G' : β → AddCommGrpCat.{u}} :
    Limits.Pi.map (fun i => (0 : G i ⟶ G' i)) = 0 := by
  apply Limits.Pi.hom_ext
  intro i
  rw [Limits.Pi.map_π]
  simp only [Limits.zero_comp]
  simp

/-- The Čech complex functor sends zero morphisms of presheaves of abelian groups to zero
morphisms of cochain complexes.  (The corresponding `PreservesZeroMorphisms` instance is
not available in Mathlib.) -/
lemma cechComplexFunctor_map_zero {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    {P Q : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}} :
    (cechComplexFunctor U).map (0 : P ⟶ Q) = 0 := by
  simp only [cechComplexFunctor, FormalCoproduct.cochainComplexFunctor, Functor.comp_map]
  apply HomologicalComplex.hom_ext
  intro n
  show (AlgebraicTopology.AlternatingCofaceMapComplex.map
      ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk ι U).cech).map
        (0 : P ⟶ Q))).f n = 0
  rw [AlgebraicTopology.AlternatingCofaceMapComplex.map]
  show (NatTrans.app ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk ι U).cech).map
    (0 : P ⟶ Q)) (SimplexCategory.mk n)) = 0
  rw [FormalCoproduct.cosimplicialObjectFunctor_map_app]
  show Limits.Pi.map (fun i : (cechN U n).I =>
    (0 : P.obj (op ((cechN U n).obj i)) ⟶ Q.obj (op ((cechN U n).obj i)))) = 0
  exact pi_map_zero

theorem cechHomology_quotient {X : AlgebraicGeometry.Scheme.{u}}
    (S : CategoryTheory.ShortComplex (SheafOfModules X.ringCatSheaf)) (hS : S.ShortExact)
    {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (hlift : ∀ (p : ℕ) (x : Fin (p + 1) → ι)
      (y : Work.DSF1.Sheaf.sectionsAt S.X₃ (⨅ a : Fin (p + 1), U (x a))),
      ∃ x' : Work.DSF1.Sheaf.sectionsAt S.X₂ (⨅ a : Fin (p + 1), U (x a)),
        Work.DSF1.Sheaf.sectionsMap S.g (⨅ a : Fin (p + 1), U (x a)) x' = y)
    (h₂ : ∀ n : ℕ, 0 < n → CategoryTheory.Limits.IsZero
      (HomologicalComplex.homology (Work.DSF1.Sheaf.cechComplex U S.X₂) n))
    (h₁ : ∀ n : ℕ, 1 < n → CategoryTheory.Limits.IsZero
      (HomologicalComplex.homology (Work.DSF1.Sheaf.cechComplex U S.X₁) n)) :
    ∀ n : ℕ, 0 < n → CategoryTheory.Limits.IsZero
      (HomologicalComplex.homology (Work.DSF1.Sheaf.cechComplex U S.X₃) n) := by
  -- The morphisms of presheaves of abelian groups underlying `S.f` and `S.g`.
  let ψf : ((SheafOfModules.toSheaf X.ringCatSheaf).obj S.X₁).obj ⟶
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj S.X₂).obj :=
    ((SheafOfModules.toSheaf X.ringCatSheaf).map S.f).hom
  let ψg : ((SheafOfModules.toSheaf X.ringCatSheaf).obj S.X₂).obj ⟶
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj S.X₃).obj :=
    ((SheafOfModules.toSheaf X.ringCatSheaf).map S.g).hom
  have hψ : ψf ≫ ψg = 0 := by
    change ((SheafOfModules.toSheaf X.ringCatSheaf).map S.f).hom ≫
      ((SheafOfModules.toSheaf X.ringCatSheaf).map S.g).hom = 0
    have h : (SheafOfModules.toSheaf X.ringCatSheaf).map S.f ≫
        (SheafOfModules.toSheaf X.ringCatSheaf).map S.g = 0 := by
      rw [← CategoryTheory.Functor.map_comp, S.zero, CategoryTheory.Functor.map_zero]
    simpa using congrArg (fun t => t.hom) h
  -- The degreewise short exact short complex of presheaves of abelian groups.
  let Tp : ShortComplex (X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) := ShortComplex.mk ψf ψg hψ
  have hzeroC : ((cechComplexFunctor U).map Tp.f) ≫ ((cechComplexFunctor U).map Tp.g) = 0 := by
    show ((cechComplexFunctor U).map ψf) ≫ ((cechComplexFunctor U).map ψg) = 0
    rw [← CategoryTheory.Functor.map_comp, hψ, cechComplexFunctor_map_zero]
  -- The induced short complex of Čech complexes.
  let Tc : ShortComplex (CochainComplex AddCommGrpCat.{u} ℕ) :=
    ShortComplex.mk ((cechComplexFunctor U).map Tp.f) ((cechComplexFunctor U).map Tp.g) hzeroC
  have hTc : Tc.ShortExact :=
    Work.DSF1.Sheaf.Work.DSF1.Sheaf.cechComplex_map_shortExact U Tp hzeroC
      (fun n x => by
        show Function.Injective (sectionsMap S.f ((cechN U n).obj x))
        exact injective_sectionsMap_of_shortExact S hS ((cechN U n).obj x))
      (fun n x => by
        show Function.Surjective (sectionsMap S.g ((cechN U n).obj x))
        have hV : (cechN U n).obj x = ⨅ a : Fin (n + 1), U (x a) := by
          rw [cechN_obj]
          exact piObj_eq_iInf (fun a : Fin (n + 1) => U (x a))
        exact hV.symm ▸ hlift n x)
      (fun n x y hy => by
        show ∃ z : sectionsAt S.X₁ ((cechN U n).obj x),
          sectionsMap S.f ((cechN U n).obj x) z = y
        exact exists_lift_of_sectionsMap_eq_zero S hS ((cechN U n).obj x) y hy)
  intro n hn
  exact isZero_homology_quotient_of_shortExact Tc hTc
    (fun m hm => h₂ m hm) (fun m hm => h₁ m hm) n hn

end Work.DSF1.Sheaf
