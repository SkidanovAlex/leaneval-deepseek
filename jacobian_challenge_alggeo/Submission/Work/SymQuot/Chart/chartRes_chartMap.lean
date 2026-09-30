/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Naturality of the chart map in the open subscheme (area SY)

For a `G`-invariant open subscheme `U ⊆ X`, the chart map `U ⟶ chart U = Spec Γ(X,U)^G`
is `U.toSpecΓ` followed by `Spec` of the inclusion `Γ(X,U)^G ↪ Γ(X,U)`.  For an inclusion
`V ≤ U` of `G`-invariant opens this construction is natural: restricting from `U` to `V` and
then applying the chart map of `V` agrees with applying the chart map of `U` first and then
the chart restriction `chart V ⟶ chart U`.
-/
import Mathlib
import Submission.Work.SymQuot.Chart

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SymQuot.Chart

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

/-- The chart map is natural with respect to restriction along an inclusion `V ≤ U` of
`G`-invariant opens: `chartMap` intertwines the restriction of the open subschemes with the
restriction of the charts. -/
theorem chartRes_chartMap {G : Type*} [Group G] {X : AlgebraicGeometry.Scheme}
    (A : Work.SymQuot.GAction G X) {V U : X.Opens} (h : V ≤ U) (hU : A.IsInvariantOpen U)
    (hVi : A.IsInvariantOpen V) :
    CategoryTheory.CategoryStruct.comp (AlgebraicGeometry.Scheme.homOfLE X h) (A.chartMap U hU) =
      CategoryTheory.CategoryStruct.comp (A.chartMap V hVi) (A.chartRes V U h hU hVi) := by
  rw [Work.SymQuot.GAction.chartMap, Work.SymQuot.GAction.chartMap,
    Work.SymQuot.GAction.chartRes]
  rw [← Category.assoc, ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map V U h, Category.assoc,
    ← Spec.map_comp, Work.SymQuot.GAction.invariantsRes_comp_subtype A V U h hU hVi,
    Spec.map_comp, Category.assoc]

end Work.SymQuot.Chart
