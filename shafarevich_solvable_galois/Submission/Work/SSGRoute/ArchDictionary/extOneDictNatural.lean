import Mathlib
import Submission.Work.SSGRoute.ArchDictionary.ExtCokerDefs
import Submission.Work.SSGRoute.ArchDictionary.ExtOneDictSetup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ArchDictionary

open CategoryTheory SSGRoute.PTExt

/-- **Transport of the connecting class along the canonical morphism of presentations.** -/
theorem comp_extClass_coverMap {G : Type} [Group G] (N : Rep.{0} SSGRoute.PTExt.Coeff G)
    (M' M : Rep.{0} SSGRoute.PTExt.Coeff G) (u : M' ⟶ M)
    (a : CategoryTheory.Abelian.Ext (coverS M).X₁ N 0) :
    (CategoryTheory.Abelian.Ext.mk₀ u).comp
        ((coverS_shortExact M).extClass.comp a (add_zero 1)) (zero_add 1)
      = (coverS_shortExact M').extClass.comp
          ((CategoryTheory.Abelian.Ext.mk₀ (coverMap M' M u).τ₁).comp a (zero_add 0))
          (add_zero 1) := by
  have hnat := ShortComplex.ShortExact.extClass_naturality (coverS_shortExact M')
    (coverS_shortExact M) (coverMap M' M u)
  have h1 : (CategoryTheory.Abelian.Ext.mk₀ u).comp
        ((coverS_shortExact M).extClass.comp a (add_zero 1)) (zero_add 1)
      = ((CategoryTheory.Abelian.Ext.mk₀ u).comp ((coverS_shortExact M).extClass)
          (zero_add 1)).comp a (add_zero 1) :=
    (Abelian.Ext.comp_assoc_of_third_deg_zero (Abelian.Ext.mk₀ u)
      ((coverS_shortExact M).extClass) a (zero_add 1)).symm
  have h2 : ((CategoryTheory.Abelian.Ext.mk₀ u).comp ((coverS_shortExact M).extClass)
        (zero_add 1)).comp a (add_zero 1)
      = ((CategoryTheory.Abelian.Ext.mk₀ (coverMap M' M u).τ₃).comp
          ((coverS_shortExact M).extClass) (zero_add 1)).comp a (add_zero 1) := rfl
  have h3 : ((CategoryTheory.Abelian.Ext.mk₀ (coverMap M' M u).τ₃).comp
        ((coverS_shortExact M).extClass) (zero_add 1)).comp a (add_zero 1)
      = ((coverS_shortExact M').extClass.comp
          (CategoryTheory.Abelian.Ext.mk₀ (coverMap M' M u).τ₁) (add_zero 1)).comp a
          (add_zero 1) :=
    congrArg (fun z => z.comp a (add_zero 1)) hnat.symm
  have h4 : ((coverS_shortExact M').extClass.comp
        (CategoryTheory.Abelian.Ext.mk₀ (coverMap M' M u).τ₁) (add_zero 1)).comp a (add_zero 1)
      = (coverS_shortExact M').extClass.comp
          ((CategoryTheory.Abelian.Ext.mk₀ (coverMap M' M u).τ₁).comp a (zero_add 0))
          (add_zero 1) :=
    Abelian.Ext.comp_assoc_of_third_deg_zero ((coverS_shortExact M').extClass)
      (Abelian.Ext.mk₀ (coverMap M' M u).τ₁) a (add_zero 1)
  exact h1.trans (h2.trans (h3.trans h4))

/-- **Naturality of the degree-zero transport** applied to the induced morphism of dual
complexes. -/
theorem unitHomExtEquiv_symm_precomp_coverMap {G : Type} [Group G]
    (N : Rep.{0} SSGRoute.PTExt.Coeff G) (M' M : Rep.{0} SSGRoute.PTExt.Coeff G) (u : M' ⟶ M)
    (a : CategoryTheory.Abelian.Ext (coverS M).X₁ N 0) :
    (Work.SSGRoute.unitHomExtEquiv (coverS M').X₁ N).symm
        ((CategoryTheory.Abelian.Ext.mk₀ (coverMap M' M u).τ₁).comp a (zero_add 0))
      = ((Work.SSGRoute.unitHomExtEquiv (coverS M).X₁ N).symm a).comp
          (CategoryTheory.Abelian.Ext.mk₀ (homCoverMap M' M u N).τ₃) (add_zero 0) := by
  have h := Work.SSGRoute.unitHomExtEquiv_symm_precomp (coverS M).X₁ (coverS M').X₁ N
    (coverMap M' M u).τ₁ a
  rw [ext_precomp_apply] at h
  rw [ext_postcomp_apply] at h
  exact h

theorem extOneDictNatural (G : Type) [Group G] (N : Rep.{0} SSGRoute.PTExt.Coeff G)
    (hdiv : ∀ (n : ℕ), 0 < n → ∀ y : N.V, ∃ x : N.V, n • x = y) :
    ∃ e : ∀ (M : Rep.{0} SSGRoute.PTExt.Coeff G),
        CategoryTheory.Abelian.Ext M N 1 ≃+
          CategoryTheory.Abelian.Ext (SSGRoute.PTExt.unitRep G) (Work.SSGRoute.homRep M N) 1,
      ∀ (M' M : Rep.{0} SSGRoute.PTExt.Coeff G) (u : M' ⟶ M)
        (x : CategoryTheory.Abelian.Ext M N 1),
        e M' ((CategoryTheory.Abelian.Ext.mk₀ u).comp x (zero_add 1))
          = (CategoryTheory.Abelian.Ext.mk₀ (Work.SSGRoute.homRepPre M M' N u)).postcomp
              (SSGRoute.PTExt.unitRep G) (add_zero 1) (e M x) := by
  classical
  have hInj : Module.Injective SSGRoute.PTExt.Coeff N.V :=
    moduleInjective_coeff_of_divisible N.V hdiv
  refine ⟨fun M => dictEquiv N hInj M, ?_⟩
  intro M' M u x
  obtain ⟨a, rfl⟩ := extConn_surjective (coverS M) (coverS_shortExact M) N x
  rw [extConn_apply (coverS M) (coverS_shortExact M) N a]
  rw [dictEquiv_extClass N hInj M a]
  rw [ext_postcomp_apply]
  rw [comp_extClass_coverMap N M' M u a]
  rw [dictEquiv_extClass N hInj M' ((CategoryTheory.Abelian.Ext.mk₀ (coverMap M' M u).τ₁).comp a
    (zero_add 0))]
  rw [unitHomExtEquiv_symm_precomp_coverMap N M' M u a]
  rw [Abelian.Ext.comp_assoc_of_second_deg_zero
    ((Work.SSGRoute.unitHomExtEquiv (coverS M).X₁ N).symm a)
    (CategoryTheory.Abelian.Ext.mk₀ (homCoverMap M' M u N).τ₃)
    ((homCoverShortExact M' N hInj).extClass)]
  rw [← ShortComplex.ShortExact.extClass_naturality
    (homCoverShortExact M N hInj) (homCoverShortExact M' N hInj) (homCoverMap M' M u N)]
  rw [← Abelian.Ext.comp_assoc_of_third_deg_zero
    ((Work.SSGRoute.unitHomExtEquiv (coverS M).X₁ N).symm a)
    ((homCoverShortExact M N hInj).extClass)
    (CategoryTheory.Abelian.Ext.mk₀ (homCoverMap M' M u N).τ₁)]
  rfl

end Work.SSGRoute.ArchDictionary
