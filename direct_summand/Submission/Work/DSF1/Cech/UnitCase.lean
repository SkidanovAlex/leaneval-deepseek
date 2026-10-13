import Mathlib
import Submission.Work.DSF1.Cech.CechSetup
import Submission.Work.DSF1.Cech.CechComponents
import Submission.Work.DSF1.Cech.UnitCaseAux

namespace Work.DSF1.Cech

universe u
open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Simplicial BigOperators

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000

theorem UnitCase {X : Scheme.{u}} {S : Type u} [CommRing S] {ι : Type u} (U : ι → X.Opens)
    (Q : X.Opensᵒᵖ ⥤ ModuleCat S) (i₀ : ι) (h : Work.DSF1.Cech.IsIsoDeletion U Q i₀) :
    (Work.DSF1.Cech.coaug U Q ≫ ((cechComplexFunctor U).obj Q).d 0 1 = 0) ∧
      (∀ (n : ℕ) (s : ((cechComplexFunctor U).obj Q).X (n + 1)),
        (((cechComplexFunctor U).obj Q).d (n + 1) (n + 2)).hom s = 0 →
          ∃ t : ((cechComplexFunctor U).obj Q).X n,
            (((cechComplexFunctor U).obj Q).d n (n + 1)).hom t = s) ∧
      Function.Injective (Work.DSF1.Cech.coaug U Q).hom ∧
      (∀ s : ((cechComplexFunctor U).obj Q).X 0,
        (((cechComplexFunctor U).obj Q).d 0 1).hom s = 0 →
          ∃ q, (Work.DSF1.Cech.coaug U Q).hom q = s) := by
  refine ⟨CoaugCycle U Q, ?_, ?_, ?_⟩
  · intro n s hs
    exact ⟨(k U Q h n).hom s, by
      have hh := congrArg (fun f : ((cechComplexFunctor U).obj Q).X (n+1) ⟶
          ((cechComplexFunctor U).obj Q).X (n+1) => f.hom s) (homotopy_succ U Q h n)
      simp only [ModuleCat.hom_add, ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.add_apply,
        LinearMap.comp_apply, LinearMap.id_apply] at hh
      rw [hs, map_zero, add_zero] at hh
      exact hh⟩
  · intro a b hab
    have h1 := congrArg (fun f : Q.obj (op ⊤) ⟶ Q.obj (op ⊤) => f.hom a)
      (coaug_comp_kTop U Q h)
    have h2 := congrArg (fun f : Q.obj (op ⊤) ⟶ Q.obj (op ⊤) => f.hom b)
      (coaug_comp_kTop U Q h)
    simp only [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply,
      LinearMap.id_apply] at h1 h2
    rw [hab] at h1
    rw [← h1, h2]
  · intro s hs
    exact ⟨(kTop U Q h).hom s, by
      have hh := congrArg (fun f : ((cechComplexFunctor U).obj Q).X 0 ⟶
          ((cechComplexFunctor U).obj Q).X 0 => f.hom s) (homotopy_zero U Q h)
      simp only [ModuleCat.hom_add, ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.add_apply,
        LinearMap.comp_apply, LinearMap.id_apply] at hh
      rw [hs, map_zero, add_zero] at hh
      exact hh⟩

end Work.DSF1.Cech
