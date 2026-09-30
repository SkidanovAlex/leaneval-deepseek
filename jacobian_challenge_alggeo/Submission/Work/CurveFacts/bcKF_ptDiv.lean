import Mathlib
import Submission.Work.GroupChunk.Interface
import Submission.Work.BcDiv.bcDiv_ptDiv
import Submission.Work.BcDiv.ramIdx_cmp
import Submission.Work.SymQuot.DivBaseInst
import Submission.Work.SpecLin.Points.Basic
import Submission.Work.KeyLemma.BaseChange.ramIdx_placeOfPoint_baseChange
import Submission.Work.Charts.divOf_constMap
import Submission.Work.SymQuot.SymGeomInst

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.CurveFacts

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical
open scoped Work.GCBasics

/-- **Item A5 of the closure design: the divisor of a rational point is compatible with base
change of the field.**  For a curve `C` over `K` and a `K`-point `x` of `C`, the base change of
the divisor `[x]` to any field `F/K` is the divisor of the base-changed point.  This supplies the
field `P0Div_ptDiv` of `Work.GroupChunk.Input` (item O13 of the closure design).

Here `Work.GroupChunk.bcKF` is `SpecLin.DivBase.bc (Algebra.ofId K F)` for the concrete instance
`Work.SymQuot.instDivBase`, whose `bc` is `(DivOf.bcSquareTower C F F').divMap`, i.e. the
ramification-weighted pullback along the canonical morphism `C_{F'} ⟶ C_F`
(`Submission/Work/SymQuot/DivBaseInst.lean`); and `Work.SpecLin.ptDiv x` is the divisor of the
closed point of `C_K` attached to `x` (`Submission/Work/SpecLin/Points/Basic.lean`).

Proof route (mirroring `Work.BcDiv.bcDiv_ptDiv`,
`Submission/Work/BcDiv/bcDiv_ptDiv.lean`).  Both sides are `Finsupp`s on the same place set
`(C.baseChange F).Place`, so it suffices to compare their coefficients at a place `Q'` of `C_F`:
* `Curve.BCSquare.divMap_apply` / `divMapCoeff` express the left-hand coefficient as
  `(ptDiv x) (under Q') * ramIdx Q'`, so it is `1` when `Q'` is the place of the base-changed
  point and `0` otherwise;
* the ramification index is `1`: the tower square is the base change of the étale morphism
  `Spec F ⟶ Spec K` (a field extension), cf. `Work.BcDiv.ramIdx_cmp` and
  `Work.KeyLemma.Curve.ramIdx_eq_one_of_fst_eq`
  (`Submission/Work/KeyLemma/BaseChange/ramIdx_placeOfPoint_baseChange.lean`);
* the place of `C_F` above the place of `x` is exactly `ptPlace (RPt.map (Algebra.ofId K F) x)`,
  by comparing the closed points via `Work.SpecLin.ptLeft_fst` (`RPt.map (Algebra.ofId K F)` is
  `specOfMap _ ≫ x`, so its section is the transport of `ptLeft x` along the tower square).
Finally `Work.SpecLin.ptDiv_apply` identifies the coefficients of the right-hand side.

**Formalisation note.**  Area `SY` already provides this statement in the exact shape needed:
`Work.Charts.ptDiv_map_bc` (`Submission/Work/Charts/divOf_constMap.lean`) proves, for the concrete
`DivBase` instance `Work.SymQuot.instDivBase` and the symmetric-power datum
`Work.SymQuot.symGeomFamily C`, that
`ptDiv (RPt.map e q) = DivBase.bc e (ptDiv q)` for every field extension `e`; the proof goes
through `Sym^1 C` using `SymGeom.divOf_map` and `SymGeom.divOf_powMap`.  Since `bcKF F` is by
definition `DivBase.bc (Algebra.ofId K F)` (the `Algebra` structure used there being the one
induced by `Algebra.ofId K F`, hence the ambient one), the result follows by symmetry. -/
theorem bcKF_ptDiv {K : Type u} [Field K] (C : Work.CurveBasics.Curve K)
    (x : Work.SpecLin.CurveFPt C K) {F : Type u} [Field F] [Algebra K F] :
    Work.GroupChunk.bcKF (C := C) F (Work.SpecLin.ptDiv x) =
      Work.SpecLin.ptDiv (Work.GCBasics.RPt.map (Algebra.ofId K F) x) :=
  (Work.Charts.ptDiv_map_bc (C := C) (Work.SymQuot.symGeomFamily C)
    (Algebra.ofId K F) x).symm

end Work.CurveFacts
