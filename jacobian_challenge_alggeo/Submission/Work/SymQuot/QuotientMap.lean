/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The quotient map `X ⟶ X/Γ` (area SY)

The quotient map is characterised by its restrictions to the charts:
`U.ι ≫ quotientMap = chartMap U ≫ chartι U`.  It is `Γ`-invariant and surjective.
-/
import Submission.Work.SymQuot.Quotient
import Submission.Work.SymQuot.Chart.exists_quotientMap
import Submission.Work.SymQuot.Chart.exists_chart_factor

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

/-- The quotient map `X ⟶ X/Γ`. -/
noncomputable def quotientMap : X ⟶ D.Quotient :=
  (Chart.exists_quotientMap D).choose

/-- The quotient map restricts to the chart map on every chart, followed by the inclusion of the
chart into the quotient. -/
theorem quotientMap_chartι (U : D.Chart) :
    U.1.ι ≫ D.quotientMap = D.action.chartMap U.1 U.2.2 ≫ D.chartι U :=
  (Chart.exists_quotientMap D).choose_spec.1 U

/-- The quotient map is `Γ`-invariant. -/
theorem quotientMap_isInvariant : D.action.IsInvariantMorphism D.quotientMap :=
  (Chart.exists_quotientMap D).choose_spec.2.1

/-- The quotient map is surjective. -/
theorem quotientMap_surjective : Function.Surjective D.quotientMap :=
  (Chart.exists_quotientMap D).choose_spec.2.2

end QuotientData

end Work.SymQuot
