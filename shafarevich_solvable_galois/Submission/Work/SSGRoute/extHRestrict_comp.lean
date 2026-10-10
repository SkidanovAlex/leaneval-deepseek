import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.ext_corestriction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory CategoryTheory.Limits

/-- `extHRestrict` is natural in the coefficients: restricting an `Ext`-cohomology class and then
pushing it along a coefficient map is the same as first pushing along the coefficient map and then
restricting (the latter along the restriction `Rep.resFunctor D.subtype.map φ` of `φ`).

This is the `Ext`-level shadow of the fact that `Rep.resFunctor D.subtype` is an exact functor and
that `Ext.mk₀` / `Ext.comp` are natural under exact functors. -/
theorem extHRestrict_comp {G : Type} [Group G] (D : Subgroup G) {A C : Rep.{0} Coeff G}
    {n : ℕ} (x : extH A n) (φ : A ⟶ C) :
    extHRestrict D (x.comp (Abelian.Ext.mk₀ φ) (add_zero n)) =
      (extHRestrict D x).comp
        (Abelian.Ext.mk₀ ((Rep.resFunctor D.subtype).map φ)) (add_zero n) := by
  -- Unfold the restriction `extHRestrict D = extHMap D.subtype (𝟙 _)`.
  rw [extHRestrict, extHRestrict, extHMap, extHMap]
  -- Drop the two trivial coefficient maps `mk₀ (𝟙 _)`.
  simp only [Abelian.Ext.comp_mk₀_id]
  -- Expose `extRes = Ext.mapExactFunctor (Rep.resFunctor D.subtype)` on the left.
  rw [extRes]
  -- Exact functors commute with `Ext.comp` and with `Ext.mk₀`.
  rw [Abelian.Ext.mapExactFunctor_comp (Rep.resFunctor D.subtype)
      (X := unitRep G) (Y := A) (Z := C),
      Abelian.Ext.mapExactFunctor_mk₀ (Rep.resFunctor D.subtype)]
  -- Expose `extRes` on the right as well.
  rw [extRes]
  -- Reassociate: `mk₀` sits in degree zero, so the third-degree-zero associativity applies.
  exact (Abelian.Ext.comp_assoc_of_third_deg_zero (Abelian.Ext.mk₀ (unitRes D.subtype))
    (x.mapExactFunctor (Rep.resFunctor D.subtype))
    (Abelian.Ext.mk₀ ((Rep.resFunctor D.subtype).map φ)) (zero_add n)).symm

end Work.SSGRoute
