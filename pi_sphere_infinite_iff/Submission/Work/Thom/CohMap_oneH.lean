import Mathlib
import Submission.Work.Thom.Cohomology
import Submission.Work.Cohomology.CupRing
import Submission.Work.Cohomology.Pullback
import Submission.Work.Cohomology.cupNaturalH

set_option backward.isDefEq.respectTransparency false

/-!
# The pullback of the unit class `1 ∈ H⁰`

The unit class `Work.Cohomology.oneH ℤ X ∈ H⁰(X;ℤ)` is the class of the augmentation
`unitCochain` (the `0`-cochain which is `1` on every vertex).  Pullback along a continuous map
`f : X → Y` (equivalently, along the induced map of simplicial sets
`TopCat.toSSet.map f`) fixes the unit cochain, because `unitCochain` takes the value `1` on every
`0`-simplex and the pullback of a cochain `α` evaluates on a simplex `σ` by evaluating `α` on the
image simplex; this is `Work.Cohomology.genEval_dualMap`.

The cohomological statement follows from the general computation rule
`Work.Cohomology.singularCohomologyMap_classOf` (pullback sends the class of a cocycle to the class
of the pulled back cocycle) together with the fact that two equal cochains represent the same
class, `Work.Cohomology.cohomologyClassOf_congr`.

## Main results

* `Work.Thom.chainComplexMap_unitCochain` — the pullback of the unit cochain is the unit cochain;
* `Work.Thom.CohMap_oneH` — pullback fixes the unit class `1 ∈ H⁰`.
-/

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Thom

open Work.Cohomology

noncomputable section

/-- The pullback of the unit `0`-cochain along a map of simplicial sets is the unit `0`-cochain:
both are the functional which is constantly `1` on the vertices, and the value of the pullback on a
vertex `σ` is the value of the original cochain on the image vertex `g σ`. -/
theorem chainComplexMap_unitCochain {R : Type} [CommRing R] {X Y : SSet} (g : X ⟶ Y) :
    ((SSet.chainComplexMap g (ModuleCat.of R R)).f 0).hom.dualMap (unitCochain R Y)
      = unitCochain R X := by
  apply cup_ext R X
  intro σ
  rw [genEval_dualMap, genEval_unitCochain, genEval_unitCochain]

/-- **Pullback fixes the unit class.**  For a continuous map `f : X → Y`, the pullback
`f^* : H⁰(Y;ℤ) → H⁰(X;ℤ)` sends the unit class to the unit class. -/
theorem CohMap_oneH {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) :
    (Work.Thom.CohMap f ℤ 0).hom (Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of Y)))
      = Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of X)) := by
  change (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.dualChainMap ℤ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom f)) 0))
      (cohomologyClassOf ℤ (TopCat.toSSet.obj (TopCat.of Y))
        (unitCochain ℤ (TopCat.toSSet.obj (TopCat.of Y)))
        (cochainDiff_unitCochain ℤ (TopCat.toSSet.obj (TopCat.of Y))))
    = cohomologyClassOf ℤ (TopCat.toSSet.obj (TopCat.of X))
        (unitCochain ℤ (TopCat.toSSet.obj (TopCat.of X)))
        (cochainDiff_unitCochain ℤ (TopCat.toSSet.obj (TopCat.of X)))
  rw [singularCohomologyMap_classOf (X := TopCat.of X) (Y := TopCat.of Y) ℤ (TopCat.ofHom f)
      (n := 0) (unitCochain ℤ (TopCat.toSSet.obj (TopCat.of Y)))
      (cochainDiff_unitCochain ℤ (TopCat.toSSet.obj (TopCat.of Y)))]
  exact cohomologyClassOf_congr ℤ (TopCat.toSSet.obj (TopCat.of X))
    (chainComplexMap_unitCochain (R := ℤ) (TopCat.toSSet.map (TopCat.ofHom f))) _ _

end

end Work.Thom
