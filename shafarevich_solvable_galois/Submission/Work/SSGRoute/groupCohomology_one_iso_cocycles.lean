import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- **`H¹(G, A)` as `Z¹(G, A) ⧸ B¹(G, A)` for Mathlib's group cohomology.**  Degree-`1` companion of
`Work.SSGRoute.groupCohomology_two_iso_cocycles`: for a commutative ring `k`, a group `G` and a
`k`-linear representation `A : Rep k G`, Mathlib's `groupCohomology A 1` is the quotient of the
`1`-cocycles `cocycles₁ A = ker (d₁₂ A)` by the `1`-coboundaries `coboundaries₁ A = range (d₀₁ A)`.
Same proof as in degree `2`: the first isomorphism principle for the surjective
`groupCohomology.H1π A : cocycles₁ A ⟶ groupCohomology A 1`, whose kernel is `coboundaries₁ A` by
`groupCohomology.H1π_eq_zero_iff`. -/
theorem groupCohomology_one_iso_cocycles (k G : Type) [CommRing k] [Group G] (A : Rep.{0} k G) :
    Nonempty (groupCohomology A 1 ≃+
      ((groupCohomology.cocycles₁ A) ⧸
        ((groupCohomology.coboundaries₁ A).comap (groupCohomology.cocycles₁ A).subtype))) := by
  let f : (groupCohomology.cocycles₁ A) →+ groupCohomology A 1 :=
    (groupCohomology.H1π A).hom.toAddMonoidHom
  have hsurj : Function.Surjective f :=
    (ModuleCat.epi_iff_surjective (groupCohomology.H1π A)).mp inferInstance
  have hker : f.ker =
      ((groupCohomology.coboundaries₁ A).comap
        (groupCohomology.cocycles₁ A).subtype).toAddSubgroup := by
    ext x
    change (groupCohomology.H1π A).hom x = 0 ↔ x ∈
      ((groupCohomology.coboundaries₁ A).comap
        (groupCohomology.cocycles₁ A).subtype).toAddSubgroup
    rw [groupCohomology.H1π_eq_zero_iff, Submodule.mem_toAddSubgroup, Submodule.mem_comap]
    rfl
  refine ⟨(QuotientAddGroup.quotientKerEquivOfSurjective f hsurj).symm.trans
    (QuotientAddGroup.congr f.ker
      ((groupCohomology.coboundaries₁ A).comap
        (groupCohomology.cocycles₁ A).subtype).toAddSubgroup
      (AddEquiv.refl (groupCohomology.cocycles₁ A)) ?_)⟩
  rw [hker]
  ext x
  simp

end Work.SSGRoute
