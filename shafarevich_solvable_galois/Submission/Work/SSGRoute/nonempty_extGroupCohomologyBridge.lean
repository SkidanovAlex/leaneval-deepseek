import Mathlib.Tactic.Have
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
import Submission.Work.SSGRoute.extH_groupCohomology_iso
import Submission.Work.SSGRoute.mapExactFunctor_id
import Submission.Work.SSGRoute.phi1_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open CategoryTheory

/-- **`extHMap` at the identity group map is postcomposition with `mk₀ φ`.**

For `f = MonoidHom.id G` the two outer factors in the definition of `extHMap`,
`mk₀ (unitRes (MonoidHom.id G))` and `extRes (MonoidHom.id G) (-)`, are the identity
(`unitRes (MonoidHom.id G) = 𝟙 (unitRep G)` by `rfl`, and `extRes (MonoidHom.id G) x = x`
by `Work.SSGRoute.mapExactFunctor_id`), so `extHMap (MonoidHom.id G) φ x` is just
`x.comp (mk₀ φ) (add_zero n)`. -/
theorem extHMap_id_coeff {G : Type} [Group G] {A B : Rep SSGRoute.PTExt.Coeff G} (φ : A ⟶ B)
    {n : ℕ} (x : SSGRoute.PTExt.extH A n) :
    SSGRoute.PTExt.extHMap (MonoidHom.id G) φ x =
      x.comp (CategoryTheory.Abelian.Ext.mk₀ φ) (add_zero n) := by
  have h1 : SSGRoute.PTExt.extRes (MonoidHom.id G) x = x := Work.SSGRoute.mapExactFunctor_id x
  have h2 : SSGRoute.PTExt.unitRes (MonoidHom.id G) = 𝟙 (SSGRoute.PTExt.unitRep G) := rfl
  rw [SSGRoute.PTExt.extHMap, h2, h1, CategoryTheory.Abelian.Ext.mk₀_id_comp]

/-- **The `Ext`/group-cohomology bridge package `E0b`, assembled from the Mathlib glue.**

`Work.SSGRoute.extH_groupCohomology_iso` supplies an existential family of additive isomorphisms
`e n G A : Hⁿ(G,A) ≃+ Extⁿ_G(ℤ,A)` which is compatible with *every* change of group followed by a
coefficient map, and compatible up to sign with connecting maps.  The package
`SSGRoute.Phi1.ExtGroupCohomologyBridge` (consumed by `Work.SSGRoute.levelPair_pushClass_bridge`
and the E3–E6 lane) only asks for the *restricted* forms of these: naturality for the identity map
of groups, i.e. only for a coefficient change at a fixed group, and the same `δ`-clause.

The only work is therefore the embedding of the restricted statements into the general ones: with
`f = MonoidHom.id G` and `φ : A ⟶ B` (viewed as `φ : Rep.res (MonoidHom.id G) A ⟶ B`),
`extHMap (MonoidHom.id G) φ x = x.comp (mk₀ φ) (add_zero n)`, because
`unitRes (MonoidHom.id G) = 𝟙 (unitRep G)` in the definition of `extHMap`
(`extRes (MonoidHom.id G) x = x` is `Work.SSGRoute.extRes_id`, and the remaining steps are
`Abelian.Ext.comp_mk₀_id` / `mk₀_id_comp`). -/
theorem nonempty_extGroupCohomologyBridge :
    Nonempty SSGRoute.Phi1.ExtGroupCohomologyBridge := by
  obtain ⟨e, hnat, hdelta⟩ := extH_groupCohomology_iso
  exact ⟨{ e := e
           naturality := fun n G _ A B φ y => by
             rw [hnat n G G (MonoidHom.id G) A B φ y, extHMap_id_coeff]
           delta := fun n G _ S hS y => hdelta n G S hS y }⟩

end Work.SSGRoute
