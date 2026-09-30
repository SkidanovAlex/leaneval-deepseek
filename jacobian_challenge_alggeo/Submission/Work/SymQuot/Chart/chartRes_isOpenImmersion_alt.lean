/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The restriction of charts along an inclusion of invariant affine opens is an open immersion

For a scheme `X` with an action of a finite group `G`, and `G`-invariant affine open subschemes
`V ≤ U`, the restriction map between the charts `chart V = Spec Γ(X,V)^G` and
`chart U = Spec Γ(X,U)^G` is an open immersion.

The proof is by the local criterion `IsOpenImmersion.of_forall_source_exists`: the chart of `V`
is covered by the charts of invariant basic opens `X.basicOpen h ⊆ V` with `h` a `G`-fixed
section over `U` (`chartRes_cover`); over such a basic open the chart restriction is a
localization, hence an open immersion (`chartRes_isOpenImmersion_basicOpen_le`), and the
composite with `chartRes V U` is `chartRes (X.basicOpen h) U`
(`chartRes_isOpenImmersion_basicOpen`), again an open immersion.  The map `chartRes V U` is
injective by `chartRes_isEmbedding`.
-/
import Mathlib
import Submission.Work.SymQuot.Chart
import Submission.Work.SymQuot.Chart.chartRes_aux
import Submission.Work.SymQuot.Chart.chartRes_cover
import Submission.Work.SymQuot.Chart.chartRes_isEmbedding

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SymQuot.Chart

theorem chartRes_isOpenImmersion_alt {G : Type*} [Group G] [Finite G] {X : AlgebraicGeometry.Scheme}
    (A : Work.SymQuot.GAction G X) {V U : X.Opens} (hVU : V ≤ U)
    (hU : AlgebraicGeometry.IsAffineOpen U) (hV : AlgebraicGeometry.IsAffineOpen V)
    (hUi : A.IsInvariantOpen U) (hVi : A.IsInvariantOpen V) :
    AlgebraicGeometry.IsOpenImmersion (Work.SymQuot.GAction.chartRes A V U hVU hUi hVi) := by
  refine IsOpenImmersion.of_forall_source_exists
    (Work.SymQuot.GAction.chartRes A V U hVU hUi hVi)
    (chartRes_isEmbedding A hVU hU hV hUi hVi).injective ?_
  intro y
  -- cover the chart of `V` by the charts of invariant basic opens of `V` coming from `U`
  obtain ⟨h, hh, hle, hz⟩ := chartRes_cover A hVU hU hV hUi hVi y
  have hW : A.IsInvariantOpen (X.basicOpen h) := isInvariantOpen_basicOpen A hUi h hh
  refine ⟨Work.SymQuot.GAction.chart A (X.basicOpen h) hW,
    Work.SymQuot.GAction.chartRes A (X.basicOpen h) V hle hVi hW,
    chartRes_isOpenImmersion_basicOpen_le A hVU hV hVi hUi h hh hle hW, ?_, ?_⟩
  · simpa using hz
  · rw [Work.SymQuot.GAction.chartRes_comp A (X.basicOpen h) V U hle hVU hUi hVi hW]
    exact chartRes_isOpenImmersion_basicOpen A hU hUi h hh hW

end Work.SymQuot.Chart
