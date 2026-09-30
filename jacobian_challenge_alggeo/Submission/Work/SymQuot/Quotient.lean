/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The quotient of a scheme by a finite group (area SY)

Given a scheme `X` with an action of a finite group `Γ` and a `Γ`-invariant affine open cover of
`X`, the quotient `X/Γ` is the *locally directed colimit* of the diagram of charts

```
D.Chart ⥤ Scheme,   U ↦ Spec Γ(X,U)^Γ,   (U ≤ V) ↦ chartRes
```

over the poset `D.Chart` of invariant affine opens.  The data of the diagram (`QuotientData` and
`D.chartFunctor`) is in `Submission.Work.SymQuot.QuotientData`, *below*
`chartFunctor_isLocallyDirected`; the colimit itself and its API live here, above it.  The two
inputs of Mathlib's locally-directed-colimit machinery are that the transition maps are open
immersions (`Chart.chartRes_isOpenImmersion_alt`) and that the diagram is locally directed
(`Chart.chartFunctor_isLocallyDirected`, which uses that the fibres of the chart map are the
orbits and that the images of two charts meet in the chart of the intersection).

## Main results

* `Work.SymQuot.QuotientData.Quotient` : the quotient `X/Γ`;
* `… .chartι` : the open immersion of a chart into the quotient, `chartι_jointly_surjective`,
  `chartι_eq_iff` (the point characterisation);
The quotient map `X ⟶ X/Γ` and its properties are in `Submission.Work.SymQuot.QuotientMap` (it
is built from `Chart.exists_quotientMap`, so it has to live above that lemma).
-/
import Submission.Work.SymQuot.QuotientData
import Submission.Work.SymQuot.Chart.chartFunctor_isLocallyDirected

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SymQuot

namespace QuotientData

variable {Γ : Type u} [Group Γ] [Fintype Γ] {X : Scheme.{u}} (D : QuotientData Γ X)

/-- The quotient `X/Γ`, as the locally directed colimit of the diagram of charts. -/
noncomputable abbrev Quotient : Scheme.{u} := colimit D.chartFunctor

/-- The open immersion of the chart of an invariant affine open into the quotient. -/
noncomputable abbrev chartι (U : D.Chart) : D.chart U ⟶ D.Quotient :=
  colimit.ι D.chartFunctor U

instance (U : D.Chart) : IsOpenImmersion (D.chartι U) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι D.chartFunctor U))

/-- Every point of the quotient lies in one of the charts. -/
theorem chartι_jointly_surjective (x : D.Quotient) :
    ∃ (U : D.Chart) (y : D.chart U), D.chartι U y = x :=
  Scheme.IsLocallyDirected.ι_jointly_surjective D.chartFunctor x

/-- The characterisation of equality of two points of the quotient in terms of the charts. -/
theorem chartι_eq_iff {U V : D.Chart} {x : D.chart U} {y : D.chart V} :
    D.chartι U x = D.chartι V y ↔
      ∃ (W : D.Chart) (hU : W ⟶ U) (hV : W ⟶ V) (z : D.chart W),
        D.chartFunctor.map hU z = x ∧ D.chartFunctor.map hV z = y :=
  Scheme.IsLocallyDirected.ι_eq_ι_iff D.chartFunctor

end QuotientData

end Work.SymQuot
