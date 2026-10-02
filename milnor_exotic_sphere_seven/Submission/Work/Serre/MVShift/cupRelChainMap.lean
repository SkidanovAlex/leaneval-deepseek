import Mathlib
import Submission.Work.Serre.MVShift.HonestCup
import Submission.Work.Serre.MVShift.ShQ
import Submission.Work.Serre.MVShift.relMapLM_mixedRelStar

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Serre.MVShift

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

theorem cupRelChainMap {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂) (f : X₁ ⟶ X₂)
    (h : ∀ x ∈ A₁, f x ∈ A₂) (n₀ : ℕ) (t : Work.Cohomology.relKern ℚ X₂ A₂ n₀)
    (ht : Work.Cohomology.relDiffLM ℚ X₂ A₂ n₀ t = 0) :
    CategoryTheory.CategoryStruct.comp (Work.Serre.cupRelChain X₂ A₂ n₀ t ht)
        (Work.Serre.MVShift.shMap
          (Work.Cohomology.relComplexMap ℚ A₁ A₂ f h) n₀)
      = CategoryTheory.CategoryStruct.comp
          (Work.Cohomology.relComplexMap (X₁ := X₁) (X₂ := X₂) ℚ (∅ : Set X₁) (∅ : Set X₂) f
            (fun _ hx => hx))
          (Work.Serre.cupRelChain X₁ A₁ n₀ (Work.Cohomology.relMapLM ℚ A₁ A₂ f h n₀ t)
            (Work.Cohomology.relDiffLM_relMapLM (R := ℚ) A₁ A₂ f h t ht)) := by
  apply HomologicalComplex.hom_ext
  intro k
  simp only [HomologicalComplex.comp_f, Work.Serre.cupRelChain_f, Work.Serre.MVShift.shMap_f,
    Work.Cohomology.relComplexMap_f]
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_ofHom]
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp only [ModuleCat.hom_ofHom, LinearMap.comp_apply]
  exact congrArg Subtype.val
    (Work.Serre.MVShift.relMapLM_mixedRelStar A₁ A₂ f h k n₀ x.1 t)

end Work.Serre.MVShift
