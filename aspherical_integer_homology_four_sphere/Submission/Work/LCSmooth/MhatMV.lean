/-
# Area `LCSmooth`: the Mayer–Vietoris sequence of `M̂`, from `rt` alone (convenience)

The field `L` of `Work.Final.FinalInputs` and the identification `hX` of its `(k,2)`-slot with the
singular homology of `M̂` are *constructed* in the area `Final/`
(`Work.Final.mhatMVLES` / `Work.Final.mhatMVLES_hX`, from the Mayer–Vietoris long exact sequence
`Work.Final.coverMVLES` of the cover `M̂ = A ∪ B`, whose only input — the degree-`0` exactness — is
proved by `Work.Final.mvRightX_zero_surjective`).

`Work.Final.FinalInputs.mhatLES` / `mhatLES_hX` package that construction, but they live inside the
`FinalInputs` namespace and therefore *take an ambient `FinalInputs` as a hypothesis*; a caller who
is constructing a `FinalInputs` from scratch (and hence has no such instance yet) cannot use them
directly.  This file repeats the three lines with `[rt : Work.Space.RTData]` in place of
`[D : FinalInputs]`, so that the Mayer–Vietoris data is available *before* `FinalInputs` exists.

This is a convenience, not part of the `cov_smooth` contract of the area: it is what lets the
assemblers of `Submission/Work/LCSmooth/Field.lean` offer the challenge theorem with `L` and `hX`
already filled in, leaving only the curvature datum and the homology identifications `eM`, `eN`,
`hsq` as inputs.  (If `Work.Final` ever exports an `rt`-only version, this becomes a duplicate.)
-/
import Submission.Work.Final.All

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

open CategoryTheory AlgebraicTopology
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.LCSmooth

noncomputable section

variable [rt : Work.Space.RTData]

/-- **The degree-`0` Mayer–Vietoris exactness for the cover `M̂ = A ∪ B`**, from `rt` alone:
`Work.Final.mvExactDegreeZero_of_mvRightX` applied to the proved surjectivity
`Work.Final.mvRightX_zero_surjective`.  No input is needed. -/
theorem mhatMVExactDegreeZero :
    Work.Final.MVExactDegreeZero (X := TopCat.of rt.Mhat) (Work.Final.mhatAset (rt := rt))
      (Work.Final.mhatBset (rt := rt)) :=
  Work.Final.mvExactDegreeZero_of_mvRightX (X := TopCat.of rt.Mhat)
    (Work.Final.mhatAset (rt := rt)) (Work.Final.mhatBset (rt := rt))
    (Work.Final.mhatAset_isOpen (rt := rt)) (Work.Final.mhatBset_isOpen (rt := rt))
    (Work.Final.mhatAset_union_mhatBset (rt := rt))
    (Work.Final.mvRightX_zero_surjective (X := TopCat.of rt.Mhat)
      (Work.Final.mhatAset (rt := rt)) (Work.Final.mhatBset (rt := rt))
      (Work.Final.mhatAset_isOpen (rt := rt)) (Work.Final.mhatBset_isOpen (rt := rt))
      (Work.Final.mhatAset_union_mhatBset (rt := rt)))

/-- **The Mayer–Vietoris long exact sequence of the cover `M̂ = A ∪ B`**, from `rt` alone: the
value of the field `L` of `Work.Final.FinalInputs`.  Its terms are `H_k(A ∩ B)`, `H_k(A) ⊞ H_k(B)`
and `H_k(A ∪ B)` (`Work.Final.mhatMVLES_H_zero/one/two`). -/
def mhatLES : Work.HomologyMV.MVLES :=
  Work.Final.mhatMVLES (rt := rt) (mhatMVExactDegreeZero (rt := rt))

/-- **The `(k,2)`-slot of `mhatLES` is the singular homology of `M̂`**: the value of the field `hX`
of `Work.Final.FinalInputs`. -/
def mhatLES_hX (k : ℕ) : (mhatLES (rt := rt)).H ((k : ℤ), 2) ≅
    LeanEval.Topology.intHomology k (TopCat.of rt.Mhat) :=
  Work.Final.mhatMVLES_hX (rt := rt) (mhatMVExactDegreeZero (rt := rt)) k

end

end Work.LCSmooth
