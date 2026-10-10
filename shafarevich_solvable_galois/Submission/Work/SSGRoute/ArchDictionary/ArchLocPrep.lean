import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.ArchDictionary.Defs
import Submission.Work.SSGRoute.PT.localDictionary_fin_injective
import Submission.Work.SSGRoute.ext_two_iso_divisible_cohomology
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Helpers for the archimedean local dictionary in degree one

This (sorry-free) module collects the generic lemmas that the archimedean dictionary
`Work.SSGRoute.ArchDictionary.archLocDictionaryEquiv` and its siblings are assembled from.
-/

namespace Work.SSGRoute.ArchDictionary

open CategoryTheory SSGRoute.PTExt

/-- **The degree-one internal-`Hom` identification.**  For any group `G` and `M N : Rep Coeff G`,
`Ext¹_G(ℤ, Hom_ℤ(M,N)) ≅ H¹(G, Hom_ℤ(M,N))` in the explicit inhomogeneous description
`Work.GroupCohomology.H1`, the internal `Hom` carrying the conjugation action of
`Work.SSGRoute.homRep`.  Degree-one companion of `Work.SSGRoute.ext_two_homRep_iso_H2`. -/
theorem ext_one_homRep_iso_H1 (G : Type) [Group G] (M N : Rep.{0} SSGRoute.PTExt.Coeff G) :
    Nonempty (CategoryTheory.Abelian.Ext (SSGRoute.PTExt.unitRep G) (Work.SSGRoute.homRep M N) 1 ≃+
      Work.GroupCohomology.H1 G (M.V →ₗ[SSGRoute.PTExt.Coeff] N.V)) := by
  obtain ⟨e1⟩ := Work.SSGRoute.ext_unitRep_iso_groupCohomology G (Work.SSGRoute.homRep M N) 1
  obtain ⟨e2⟩ := Work.SSGRoute.H1_coeff_transfer (k := SSGRoute.PTExt.Coeff)
    (k' := SSGRoute.PTExt.Coeff) (G := G) ((Rep.ihom M).obj N) (Work.SSGRoute.homRep M N)
    (Work.SSGRoute.bridgeEquiv M N) (Work.SSGRoute.bridgeEquiv_rho M N)
  obtain ⟨e3⟩ := Work.SSGRoute.groupCohomology_ihom_deg_one G M N
  exact ⟨e1.trans (e2.symm.trans e3)⟩

end Work.SSGRoute.ArchDictionary
