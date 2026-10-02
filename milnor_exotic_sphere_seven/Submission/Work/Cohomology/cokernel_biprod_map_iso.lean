import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace Work.Cohomology

theorem cokernel_biprod_map_iso {C : Type*} [CategoryTheory.Category C]
    [CategoryTheory.Abelian C] {A B A' B' : C}
    (f : A ⟶ B) (g : A' ⟶ B') :
    Nonempty (CategoryTheory.Limits.cokernel (CategoryTheory.Limits.biprod.map f g) ≅
      CategoryTheory.Limits.cokernel f ⊞ CategoryTheory.Limits.cokernel g) := by
  refine ⟨?_⟩
  let ψ := CategoryTheory.Limits.biprod.map f g
  let φ := CategoryTheory.Limits.biprod.map (CategoryTheory.Limits.cokernel.π f)
    (CategoryTheory.Limits.cokernel.π g)
  have hw : ψ ≫ φ = 0 := by
    dsimp only [ψ, φ]
    apply CategoryTheory.Limits.biprod.hom_ext' <;> simp
  have hcolim : CategoryTheory.Limits.IsColimit (CategoryTheory.Limits.CokernelCofork.ofπ φ hw) := by
    apply CategoryTheory.Limits.CokernelCofork.IsColimit.ofπ'
    intro W k hk
    refine ⟨CategoryTheory.Limits.biprod.desc
      (CategoryTheory.Limits.cokernel.desc f (CategoryTheory.Limits.biprod.inl ≫ k) ?_)
      (CategoryTheory.Limits.cokernel.desc g (CategoryTheory.Limits.biprod.inr ≫ k) ?_), ?_⟩
    · rw [← CategoryTheory.Category.assoc, ← CategoryTheory.Limits.biprod.inl_map,
        CategoryTheory.Category.assoc, hk, CategoryTheory.Limits.comp_zero]
    · rw [← CategoryTheory.Category.assoc, ← CategoryTheory.Limits.biprod.inr_map,
        CategoryTheory.Category.assoc, hk, CategoryTheory.Limits.comp_zero]
    · apply CategoryTheory.Limits.biprod.hom_ext' <;> simp [φ]
  exact CategoryTheory.Limits.IsColimit.coconePointUniqueUpToIso
    (CategoryTheory.Limits.cokernelIsCokernel ψ) hcolim

end Work.Cohomology
