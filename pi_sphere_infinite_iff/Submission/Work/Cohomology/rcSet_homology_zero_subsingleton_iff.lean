import Mathlib
import Submission.Work.Cohomology.wsfDefs

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

/-- In degree `0` the relative cochain complex `C^*(U, U∩A)` has no incoming differential, so its
homology in degree `0` is `ker (rcDiff A U 0)`.  Consequently it is a subsingleton exactly when
the differential `rcDiff A U 0` on relative `0`-cochains is injective. -/
theorem rcSet_homology_zero_subsingleton_iff {X : Type} [TopologicalSpace X] (A : Set X) (U : Set X) :
    Subsingleton ((rcSet A U).homology 0) ↔
      (∀ z : ↥(rcKern A U 0), rcDiff A U 0 z = 0 → z = 0) := by
  -- the two shape indices around `0`: there is no `-1`, and the next index is `1`
  have hnext : (ComplexShape.up ℕ).next 0 = 1 :=
    ComplexShape.next_eq' _ (ComplexShape.up_mk 0 1 (by norm_num))
  have hprev : (ComplexShape.up ℕ).prev 0 = 0 :=
    ComplexShape.prev_eq_self' _ 0 (by intro k hk; simp [ComplexShape.up] at hk)
  -- transfer to the explicit short complex `K.X 0 ⟶ K.X 0 ⟶ K.X 1`
  have e : (rcSet A U).sc 0 ≅ (rcSet A U).sc' 0 0 1 := (rcSet A U).isoSc' 0 0 1 hprev hnext
  have key : Subsingleton ((rcSet A U).homology 0) ↔ ((rcSet A U).sc' 0 0 1).Exact :=
    ((ModuleCat.isZero_iff_subsingleton (M := ((rcSet A U).sc 0).homology)).symm.trans
      (ShortComplex.exact_iff_isZero_homology _).symm).trans (ShortComplex.exact_iff_of_iso e)
  -- exactness of the short complex is `range f = ker g`, and `f` is the zero map
  have key2 : ((rcSet A U).sc' 0 0 1).Exact ↔ (rcDiff A U 0).ker = ⊥ := by
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    have h1 : LinearMap.range (ModuleCat.Hom.hom ((rcSet A U).sc' 0 0 1).f) = ⊥ := by
      rw [show ModuleCat.Hom.hom ((rcSet A U).sc' 0 0 1).f =
          (0 : ↥(rcKern A U 0) →ₗ[ℤ] ↥(rcKern A U 0)) from by
        show ModuleCat.Hom.hom ((rcSet A U).d 0 0) = 0
        rw [HomologicalComplex.shape (rcSet A U) 0 0
          (by intro h; simp [ComplexShape.up] at h), ModuleCat.hom_zero]]
      simp
    have h2 : LinearMap.ker (ModuleCat.Hom.hom ((rcSet A U).sc' 0 0 1).g) = (rcDiff A U 0).ker := by
      rw [show ModuleCat.Hom.hom ((rcSet A U).sc' 0 0 1).g = rcDiff A U 0 from by
        show ModuleCat.Hom.hom ((rcSet A U).d 0 1) = rcDiff A U 0
        rw [rcSet_d, ModuleCat.hom_ofHom]]
    rw [h1, h2, eq_comm]
  rw [key, key2]
  exact LinearMap.ker_eq_bot'

end

end Work.Cohomology
