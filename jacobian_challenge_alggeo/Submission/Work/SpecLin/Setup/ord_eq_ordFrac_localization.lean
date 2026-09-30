/-
# The order dictionary of an affine chart of a curve

`Scheme.ord` at a point of a curve is `Ring.ordFrac` of the *stalk* of the structure sheaf at
that point.  This file identifies it with `Ring.ordFrac` of the corresponding *localisation of
the coordinate ring of an affine chart* containing the point:

* `Work.SpecLin.Setup.ord_eq_ordFrac_localization`.

This is the bridge needed to compute, inside the coordinate ring of a chart, the order of
vanishing of a rational function at a place of the chart — the "order dictionary" input of the
affine-chart proof of specialisation of linear equivalence over a valuation ring
(`Submission/Work/SpecLin/Core/NOTES_crux.md`, `Alt/NOTES_chartCoreDiv.md`, and
`Submission/Work/SpecLin/Setup/NOTES.md`).

The single ring-theoretic input is
`Work.SpecLin.Setup.ordFrac_eq_of_isLocalizationAtPrime`: two localisations of a domain at the
same prime, both sitting inside a common fraction field, compute the same order of vanishing.

The remaining half of the dictionary (the comparison between the coordinate ring
`Γ(C,W) ⊗[K] R` of the relative chart and the chart of the generic fibre, and between the
primes of these two rings) is recorded in `Submission/Work/SpecLin/Setup/NOTES.md`.
-/
import Mathlib
import Submission.Work.CurveBasics.Place.Valuation
import Submission.Work.SpecLin.Alt.chartField
import Submission.Work.SpecLin.Setup.ordFrac_eq_of_isLocalizationAtPrime

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace Work.SpecLin.Setup

/-- **The order dictionary of an affine chart of a curve.**

`C` is a curve over `k`, `U ⊆ C` a nonempty affine open (`hU`), `Q` a place of `C` whose point
lies in `U`, and `P` the prime of `Γ(C,U)` corresponding to `Q` (`hP`).  Then the order of
vanishing of a rational function `h` at `Q` — which is `Scheme.ordHom Q.point Q.eq_coheight_one`
at `h`, i.e. `Ring.ordFrac` of the stalk of `C` at `Q.point` — equals `Ring.ordFrac` of the
localisation of the coordinate ring `Γ(C,U)` at the prime `P`.

The instance arguments are hypotheses because the algebra structure
`Algebra (Localization.AtPrime P.asIdeal) C.functionField` and its fraction-ring structure are
not instances in Mathlib: a caller obtains them from
`IsFractionRing.isFractionRing_of_isDomain_of_isLocalization` and `IsLocalization.lift`, and the
stalk side `IsLocalization.AtPrime (C.left.presheaf.stalk Q.point) P.asIdeal` from
`IsAffineOpen.isLocalization_stalk'`. -/
theorem ord_eq_ordFrac_localization {k : Type u} [Field k] (C : Work.CurveBasics.Curve k)
    (U : C.left.Opens) (hU : IsAffineOpen U) [Nonempty U] (Q : C.Place) (hQ : Q.point ∈ U)
    (P : PrimeSpectrum Γ(C.left, U)) (hP : hU.fromSpec P = Q.point)
    [Algebra (Localization.AtPrime P.asIdeal) C.functionField]
    [IsScalarTower Γ(C.left, U) (Localization.AtPrime P.asIdeal) C.functionField]
    [IsFractionRing (Localization.AtPrime P.asIdeal) C.functionField]
    [IsNoetherianRing (Localization.AtPrime P.asIdeal)]
    [Ring.KrullDimLE 1 (Localization.AtPrime P.asIdeal)]
    [Nontrivial (Localization.AtPrime P.asIdeal)]
    [Algebra Γ(C.left, U) (C.left.presheaf.stalk Q.point)]
    [IsScalarTower Γ(C.left, U) (C.left.presheaf.stalk Q.point) C.functionField]
    (hloc : IsLocalization.AtPrime (C.left.presheaf.stalk Q.point) P.asIdeal)
    (h : C.functionField) :
    C.left.ordHom Q.point Q.eq_coheight_one h
      = Ring.ordFrac (K := C.functionField) (Localization.AtPrime P.asIdeal) h := by
  haveI hff : IsFractionRing Γ(C.left, U) C.functionField :=
    Work.SpecLin.Alt.isFractionRing_functionField U hU
  have hfun := ordFrac_eq_of_isLocalizationAtPrime (A := Γ(C.left, U)) (P := P.asIdeal)
    (S := Localization.AtPrime P.asIdeal) (T := C.left.presheaf.stalk Q.point)
    (K := C.functionField)
  show Ring.ordFrac (K := C.functionField) (C.left.presheaf.stalk Q.point) h
      = Ring.ordFrac (K := C.functionField) (Localization.AtPrime P.asIdeal) h
  rw [← hfun]

end Work.SpecLin.Setup
