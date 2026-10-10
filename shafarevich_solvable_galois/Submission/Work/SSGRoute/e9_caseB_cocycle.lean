import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.eCoh_map
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- **The `1`-coboundaries, unfolded.**  A function `w : G → A` with values in the module of a
representation `A` of a group `G` is a `1`-coboundary if and only if it is of the form
`g ↦ A.ρ g m - m` for some `m : A`.

Stated over an arbitrary commutative coefficient ring (where the unfolding of
`groupCohomology.coboundaries₁` through `LinearMap.mem_range` elaborates smoothly); it is
instantiated below at `SSGRoute.PTExt.Coeff`, whose underlying ring `ULift ℤ` carries a competing
`ULift.module` instance (see `Submission/NK/HassePrinciple/...`), so that the unfolding is best
done once, at a generic coefficient ring. -/
lemma mem_coboundaries₁_iff {k : Type} [CommRing k] {G : Type} [Group G]
    (A : Rep k G) (w : G → A) :
    w ∈ groupCohomology.coboundaries₁ A ↔ ∃ m : A, ∀ g : G, w g = A.ρ g m - m := by
  rw [groupCohomology.coboundaries₁, LinearMap.mem_range]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, fun g => ?_⟩
    have h := congrFun hm g
    rw [groupCohomology.d₀₁_hom_apply] at h
    exact h.symm
  · rintro ⟨m, hm⟩
    refine ⟨m, funext fun g => ?_⟩
    rw [groupCohomology.d₀₁_hom_apply]
    exact (hm g).symm

/-- **The degree-one cocycle criterion for an arbitrary coefficient module.**  For a group `G`, a
`G`-module `A` (as a `Rep` over `Coeff`), a subgroup `D ≤ G` and a `1`-cocycle `z` of `A`, the
restriction to `D` of the class `eCoh 1 G A (H1π A z)` vanishes if and only if the restriction of
the function `z` to `D` is a coboundary, i.e. `z d = A.ρ d m - m` for some `m : A` and all
`d ∈ D`.

Route: `eCoh_map` (naturality of `eCoh` under `groupCohomology.map`, with `f = D.subtype` and
`φ = id`) turns `extHRestrict D (eCoh 1 G A y)` into `eCoh 1 ↥D (Rep.res D.subtype A)` applied to
`(groupCohomology.map D.subtype id 1).hom y`; `eCoh` is injective, so the vanishing is equivalent to
`(map D.subtype id 1) (H1π A z) = 0`, which by `groupCohomology.H1π_comp_map_apply` is
`H1π (Rep.res D.subtype A) (mapCocycles₁ D.subtype id z) = 0`, i.e. by
`groupCohomology.H1π_eq_zero_iff` the restricted cocycle is in `coboundaries₁`, i.e. equals
`(d₀₁ _).hom m` for some `m`; `groupCohomology.d₀₁_hom_apply` computes this as `d • m - m`, and
`groupCohomology.coe_mapCocycles₁` computes the restriction of the cocycle as `z ∘ D.subtype`. -/
theorem e9_caseB_cocycle {G : Type} [Group G] (A : Rep.{0} SSGRoute.PTExt.Coeff G)
    (D : Subgroup G) (z : ↥(groupCohomology.cocycles₁ A)) :
    SSGRoute.PTExt.extHRestrict D (SSGRoute.PTExt.eCoh 1 G A
        ((groupCohomology.H1π A).hom z)) = 0 ↔
      ∃ m : ↥A, ∀ d ∈ D, (z : G → ↥A) d = A.ρ d m - m := by
  -- The restriction of the class `eCoh 1 G A (H1π A z)` to `D` is computed by naturality of `eCoh`.
  have hmap : SSGRoute.PTExt.extHRestrict D
      (SSGRoute.PTExt.eCoh 1 G A ((groupCohomology.H1π A).hom z)) =
      SSGRoute.PTExt.eCoh 1 (↥D) (Rep.res D.subtype A)
        ((groupCohomology.map D.subtype (CategoryTheory.CategoryStruct.id (Rep.res D.subtype A)) 1).hom
          ((groupCohomology.H1π A).hom z)) := by
    rw [SSGRoute.PTExt.extHRestrict]
    exact (eCoh_map 1 G (↥D) D.subtype A (Rep.res D.subtype A)
      (CategoryTheory.CategoryStruct.id (Rep.res D.subtype A)) ((groupCohomology.H1π A).hom z)).symm
  -- The restricted cocycle `mapCocycles₁ D.subtype id z` is the naive restriction of `z` to `D`.
  have hcoe : ⇑((groupCohomology.mapCocycles₁ D.subtype (CategoryTheory.CategoryStruct.id (Rep.res D.subtype A))) z)
      = fun d : ↥D => (z : G → ↥A) (D.subtype d) := by
    funext d
    rw [groupCohomology.coe_mapCocycles₁]
    rfl
  rw [hmap, AddEquiv.map_eq_zero_iff, groupCohomology.H1π_comp_map_apply,
    groupCohomology.H1π_eq_zero_iff]
  rw [mem_coboundaries₁_iff (Rep.res D.subtype A) _]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, fun d hd => ?_⟩
    have h := hm ⟨d, hd⟩
    rw [hcoe] at h
    simpa using h
  · rintro ⟨m, hm⟩
    refine ⟨m, fun g => ?_⟩
    rw [hcoe]
    exact hm (D.subtype g) g.2

end Work.SSGRoute
