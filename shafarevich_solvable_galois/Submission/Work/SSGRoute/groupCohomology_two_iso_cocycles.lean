import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Submission.Work.GroupCohomology.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `H²(G, A)` as `Z²(G, A) ⧸ B²(G, A)` for Mathlib's group cohomology

For a commutative ring `k`, a group `G` and a `k`-linear representation `A : Rep k G`, Mathlib's
group cohomology `groupCohomology A 2` is the second cohomology of the complex of inhomogeneous
cochains, hence the quotient of the `2`-cocycles `cocycles₂ A = ker (d₂₃ A)` by the `2`-coboundaries
`coboundaries₂ A = range (d₁₂ A)`.  The proof is the first isomorphism theorem for the surjective map
`groupCohomology.H2π A : cocycles₂ A ⟶ groupCohomology A 2`, whose kernel is `coboundaries₂ A` by
`groupCohomology.H2π_eq_zero_iff`.
-/

open CategoryTheory

namespace Work.SSGRoute

theorem groupCohomology_two_iso_cocycles (k G : Type) [CommRing k] [Group G]
    (A : Rep.{0} k G) :
    Nonempty (groupCohomology A 2 ≃+
      ((groupCohomology.cocycles₂ A) ⧸
        ((groupCohomology.coboundaries₂ A).comap (groupCohomology.cocycles₂ A).subtype))) := by
  let f : (groupCohomology.cocycles₂ A) →+ groupCohomology A 2 :=
    (groupCohomology.H2π A).hom.toAddMonoidHom
  have hsurj : Function.Surjective f :=
    (ModuleCat.epi_iff_surjective (groupCohomology.H2π A)).mp inferInstance
  have hker : f.ker =
      ((groupCohomology.coboundaries₂ A).comap
        (groupCohomology.cocycles₂ A).subtype).toAddSubgroup := by
    ext x
    change (groupCohomology.H2π A).hom x = 0 ↔ x ∈
      ((groupCohomology.coboundaries₂ A).comap
        (groupCohomology.cocycles₂ A).subtype).toAddSubgroup
    rw [groupCohomology.H2π_eq_zero_iff, Submodule.mem_toAddSubgroup, Submodule.mem_comap]
    rfl
  refine ⟨(QuotientAddGroup.quotientKerEquivOfSurjective f hsurj).symm.trans
    (QuotientAddGroup.congr f.ker
      ((groupCohomology.coboundaries₂ A).comap
        (groupCohomology.cocycles₂ A).subtype).toAddSubgroup
      (AddEquiv.refl (groupCohomology.cocycles₂ A)) ?_)⟩
  rw [hker]
  ext x
  simp

end Work.SSGRoute
