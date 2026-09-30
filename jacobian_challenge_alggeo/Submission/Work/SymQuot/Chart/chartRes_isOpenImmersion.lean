import Mathlib
import Submission.Work.SymQuot.Chart
import Submission.Work.SymQuot.Chart.chartRes_isEmbedding
import Submission.Work.SymQuot.Chart.chartRes_isOpen_range
import Submission.Work.SymQuot.Chart.chartRes_stalkMap_isIso

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SymQuot.Chart

/-- The restriction morphism between the charts of two `G`-invariant affine opens `V ≤ U` of a
scheme with an action of a finite group `G` is an open immersion.

It is the morphism `Spec Γ(X,V)^G ⟶ Spec Γ(X,U)^G` induced by the restriction of sections; it
identifies `chart V` with the open subscheme `q(V)` of `chart U`, where `q : U ⟶ chart U` is the
quotient map.

The proof combines three ingredients:
* its underlying map of points is an embedding (`chartRes_isEmbedding`);
* its range is open (`chartRes_isOpen_range`);
* it is an isomorphism on stalks (`chartRes_stalkMap_isIso`),
and Mathlib's criterion `IsOpenImmersion.iff_isIso_stalkMap` for open immersions. -/
theorem chartRes_isOpenImmersion {G : Type*} [Group G] [Finite G] {X : AlgebraicGeometry.Scheme}
    (A : Work.SymQuot.GAction G X) {V U : X.Opens} (hVU : V ≤ U)
    (hU : AlgebraicGeometry.IsAffineOpen U) (hV : AlgebraicGeometry.IsAffineOpen V)
    (hUi : A.IsInvariantOpen U) (hVi : A.IsInvariantOpen V) :
    AlgebraicGeometry.IsOpenImmersion (Work.SymQuot.GAction.chartRes A V U hVU hUi hVi) := by
  have hEmb : Topology.IsEmbedding ⇑(Work.SymQuot.GAction.chartRes A V U hVU hUi hVi) :=
    chartRes_isEmbedding A hVU hU hV hUi hVi
  have hOpen : IsOpen (Set.range ⇑(Work.SymQuot.GAction.chartRes A V U hVU hUi hVi)) :=
    chartRes_isOpen_range A hVU hU hV hUi hVi
  have hStalk : ∀ y, CategoryTheory.IsIso
      ((Work.SymQuot.GAction.chartRes A V U hVU hUi hVi).stalkMap y) :=
    fun y => chartRes_stalkMap_isIso A hVU hU hV hUi hVi y
  rw [IsOpenImmersion.iff_isIso_stalkMap]
  exact ⟨⟨hEmb, hOpen⟩, hStalk⟩

end Work.SymQuot.Chart
