import Submission.Work.Cohomology.exists_relComplexMap

/-!
# Contravariant functoriality of the pullback of relative cochain complexes

`Work.Cohomology.relComplexMap A₁ A₂ f h : C^*(X₂, A₂) ⟶ C^*(X₁, A₁)` is the pullback along a map
of pairs `f : (X₁,A₁) → (X₂,A₂)`.  This file records that it is (contravariantly) functorial:

`relComplexMap A₁ A₃ (f ≫ g) … = relComplexMap A₂ A₃ g … ≫ relComplexMap A₁ A₂ f …`.

This is the glue needed to *factor* the restriction map of the transgression identity,
`H⁴(Vk,Mk) → H⁴(overlap, ovlA)`, through the chart pair `(U, U∩A)` (`Endgame/NOTES.md` §28, step 1
of the plan for `Endgame/vk_ovlRestr_ne_zero`).
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Cohomology

noncomputable section

/-- **Contravariant functoriality of `relComplexMap`.** -/
theorem relComplexMapComp {X₁ X₂ X₃ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂) (A₃ : Set X₃)
    (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (h₁ : ∀ x ∈ A₁, f x ∈ A₂) (h₂ : ∀ y ∈ A₂, g y ∈ A₃) :
    relComplexMap ℤ A₁ A₃ (f ≫ g) (fun x hx => h₂ (f x) (h₁ x hx))
      = relComplexMap ℤ A₂ A₃ g h₂ ≫ relComplexMap ℤ A₁ A₂ f h₁ := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  show ((relMapLM ℤ A₁ A₃ (f ≫ g) (fun x hx => h₂ (f x) (h₁ x hx)) n) x).1
      = ((relMapLM ℤ A₁ A₂ f h₁ n) ((relMapLM ℤ A₂ A₃ g h₂ n) x)).1
  simp only [relComplexMap_f, dualChainMap_comp, HomologicalComplex.comp_f, ModuleCat.hom_comp,
    LinearMap.comp_apply, ModuleCat.hom_ofHom, relMapLM_coe]

end

end Work.Cohomology
