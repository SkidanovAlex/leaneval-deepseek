import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.e0b_bridge
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

universe u

/-- **Group cohomology of a finite group with finite coefficients is finite.**  The inhomogeneous
`n`-cochains `(Fin n → G) → A` form a finite type (`G` and `A` are finite), the `n`-cocycles are a
subtype of it (a kernel), and `Hⁿ(G, A)` is a quotient of the `n`-cocycles, hence finite. -/
theorem finite_groupCohomology_of_finite {k G : Type u} [CommRing k] [Group G] [Finite G]
    (A : Rep k G) [Finite A] (n : ℕ) : Finite (groupCohomology A n) := by
  -- `Zⁿ(G, A)` is a subobject of the finite type `Cⁿ(G, A)`.
  have : Finite ↥((groupCohomology.inhomogeneousCochains A).cycles n) :=
    Finite.of_injective (fun x => (groupCohomology.inhomogeneousCochains A).iCycles n x)
      ((ModuleCat.mono_iff_injective _).mp inferInstance)
  -- `Hⁿ(G, A)` is a quotient of `Zⁿ(G, A)`.
  have hπ : Function.Surjective ⇑((groupCohomology.inhomogeneousCochains A).homologyπ n) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  exact Finite.of_surjective _ hπ

/-- `Hⁿ(G, A) = extH A n` is finite for a finite group `G` and a finite module `A` (the group of
cochains `(Fin n → G) → A` is finite, and cohomology is a subquotient of it; transfer along the
bar-resolution bridge `Work.SSGRoute.Bridge.E`). -/
theorem local_duality_ext_extH_finite {G : Type} [Group G] [Finite G] (A : Rep Coeff G) [Finite A]
    (n : ℕ) : Finite (extH A n) := by
  have : Finite (groupCohomology A n) := finite_groupCohomology_of_finite A n
  exact Finite.of_equiv _ (Bridge.E n G A).toEquiv

end Work.SSGRoute
