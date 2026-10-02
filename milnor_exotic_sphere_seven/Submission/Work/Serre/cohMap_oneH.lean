import Mathlib
import Submission.Work.Thom.Cohomology
import Submission.Work.Thom.CohMap_oneH
import Submission.Work.Cohomology.CupRing

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Pullback of the unit class `1 ∈ H⁰`, with coefficients in an arbitrary commutative ring

`Submission/Work/Thom/CohMap_oneH.lean` proves that for a continuous map `f : X → Y` the pullback
`f^* : H⁰(Y;ℤ) → H⁰(X;ℤ)` fixes the unit class.  The whole argument is insensitive to the
coefficient ring: the unit `0`-cochain `unitCochain R` takes the value `1` on every vertex, the
evaluation rule `genEval_dualMap` computes the pullback of a cochain on a simplex as the value on
the image simplex, and `singularCohomologyMap_classOf` identifies the pullback on cohomology with
the class of the pulled-back cocycle.  All of these are stated for an arbitrary commutative ring,
so the same three steps prove the general statement.

This is the `n = 0` ingredient of the multiplicativity of the pullback on the cohomology ring of
the Milnor exotic sphere chapter: the cohomology unit behaves naturally, `f^*(1) = 1`.

## Main results

* `Work.Serre.cohMap_oneH` — pullback fixes the unit class `1 ∈ H⁰`, for any commutative
  coefficient ring `R`.
-/

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Serre

open Work.Cohomology

noncomputable section

/-- **Pullback fixes the unit class, with coefficients in an arbitrary commutative ring.**
For a continuous map `f : B₁ → B₂` and any commutative ring `R`, the pullback
`f^* : H⁰(B₂;R) → H⁰(B₁;R)` sends the unit class to the unit class. -/
theorem cohMap_oneH (R : Type) [CommRing R] {B₁ B₂ : Type} [TopologicalSpace B₁]
    [TopologicalSpace B₂] (f : C(B₁, B₂)) :
    (Work.Thom.CohMap f R 0).hom (Work.Cohomology.oneH R (TopCat.toSSet.obj (TopCat.of B₂)))
      = Work.Cohomology.oneH R (TopCat.toSSet.obj (TopCat.of B₁)) := by
  change (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.dualChainMap R (TopCat.of B₁) (TopCat.of B₂) (TopCat.ofHom f)) 0))
      (cohomologyClassOf R (TopCat.toSSet.obj (TopCat.of B₂))
        (unitCochain R (TopCat.toSSet.obj (TopCat.of B₂)))
        (cochainDiff_unitCochain R (TopCat.toSSet.obj (TopCat.of B₂))))
    = cohomologyClassOf R (TopCat.toSSet.obj (TopCat.of B₁))
        (unitCochain R (TopCat.toSSet.obj (TopCat.of B₁)))
        (cochainDiff_unitCochain R (TopCat.toSSet.obj (TopCat.of B₁)))
  rw [singularCohomologyMap_classOf (X := TopCat.of B₁) (Y := TopCat.of B₂) R (TopCat.ofHom f)
      (n := 0) (unitCochain R (TopCat.toSSet.obj (TopCat.of B₂)))
      (cochainDiff_unitCochain R (TopCat.toSSet.obj (TopCat.of B₂)))]
  exact cohomologyClassOf_congr R (TopCat.toSSet.obj (TopCat.of B₁))
    (Work.Thom.chainComplexMap_unitCochain (R := R) (TopCat.toSSet.map (TopCat.ofHom f))) _ _

end

end Work.Serre
