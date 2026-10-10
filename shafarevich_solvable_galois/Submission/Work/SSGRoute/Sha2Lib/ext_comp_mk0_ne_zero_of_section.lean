import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.Sha2Lib

open CategoryTheory

/-- If `j : B ⟶ A` admits a section `s : A ⟶ B` (`s ≫ j = 𝟙 A`, i.e. `j` is a split
epimorphism) then the precomposition map `Ext^n(A, C) → Ext^n(B, C)`,
`φ ↦ mk₀ j ≫ φ`, is injective: it has the left inverse `ψ ↦ mk₀ s ≫ ψ`, because
`mk₀ s ≫ (mk₀ j ≫ φ) = mk₀ (s ≫ j) ≫ φ = mk₀ (𝟙 A) ≫ φ = φ`. -/
theorem ext_comp_mk0_ne_zero_of_section {G : Type} [Group G] {A B C : Rep.{0} SSGRoute.PTExt.Coeff G}
    (j : B ⟶ A) (s : A ⟶ B)
    (hs : CategoryTheory.CategoryStruct.comp s j = CategoryTheory.CategoryStruct.id A) {n : ℕ}
    {φ : CategoryTheory.Abelian.Ext.{0} A C n} (hφ : φ ≠ 0) :
    (CategoryTheory.Abelian.Ext.mk₀ j).comp φ (zero_add n) ≠ 0 := by
  intro h
  apply hφ
  have h2 : (CategoryTheory.Abelian.Ext.mk₀ s).comp
      ((CategoryTheory.Abelian.Ext.mk₀ j).comp φ (zero_add n)) (zero_add n) = 0 := by
    rw [h, CategoryTheory.Abelian.Ext.comp_zero]
  rw [CategoryTheory.Abelian.Ext.mk₀_comp_mk₀_assoc] at h2
  rw [hs] at h2
  simpa using h2

end Work.SSGRoute.Sha2Lib
