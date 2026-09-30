import Mathlib
import Submission.Work.SpecLin.Chart.Regular
import Submission.Work.SpecLin.Chart.RegularOpensMap
import Submission.Work.SpecLin.Chart.RegularOpensAffineAux
import Submission.Work.SpecLin.Chart.valuativeCriterion_regularOpensMap
import Submission.Work.SpecLin.Chart.locallyQuasiFinite_regularOpensMap

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.SpecLin.Chart

open CategoryTheory AlgebraicGeometry

/-- Assembly of `isAffineOpen_regularOpens` from the properness (valuative criterion) and
local quasi-finiteness of the coordinate morphism `regularOpensMap C x`. -/
theorem isAffineOpen_regularOpensAux {K : Type*} [Field K] (C : Work.CurveBasics.Curve K)
    (x : C.functionField) (hx : Transcendental K x) :
    IsAffineOpen (regularOpens C x) := by
  haveI hproper : IsProper (regularOpensMap C x) :=
    isProper_regularOpensMap_of_valuativeCriterion C x
      (valuativeCriterion_regularOpensMap C x hx)
  haveI hlqf : LocallyQuasiFinite (regularOpensMap C x) :=
    locallyQuasiFinite_regularOpensMap C x hx
  haveI hfin : IsFinite (regularOpensMap C x) :=
    IsFinite.of_isProper_of_locallyQuasiFinite (regularOpensMap C x)
  haveI : IsAffine (Spec (CommRingCat.of (Polynomial K))) := inferInstance
  exact isAffine_of_isAffineHom (regularOpensMap C x)

end Work.SpecLin.Chart
