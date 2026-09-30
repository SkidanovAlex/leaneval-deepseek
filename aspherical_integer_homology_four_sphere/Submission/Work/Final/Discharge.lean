/-
# `Final/`: discharging the fields of `Work.Final.FinalInputs`

Three of the fields of `Work.Final.FinalInputs` can now be **derived** from the rest, using the
lemmas that the other areas have delivered:

* the field `L` (the Mayer–Vietoris long exact sequence of the cover `M̂ = A ∪ B`) is
  `Work.Final.FinalInputs.mhatLES`, built from `Work.Final.coverMVLES` applied to the cover
  `Work.Space.Assembly.Aset_sup_Bset`; the only input is the degree-`0` exactness
  `Work.Final.MVExactDegreeZero`, which is **proved** by
  `Work.Final.mvRightX_zero_surjective` (delegated from this area) via
  `Work.Final.mvExactDegreeZero_of_mvRightX` — so `L` needs no further input at all;
* the field `hX` (the `(k,2)`-slot is the singular homology of `M̂`) is
  `Work.Final.FinalInputs.mhatLES_hX`, from `Work.Final.coverMVLES_hX`;
* the field `curvLe` is `Work.Final.FinalInputs.curvLe_of_models`, which is the curvature bridge
  `Work.Final.secNonpos_of_chartModels` (delegated from this area) applied pointwise, composed with
  `Work.CartanHadamard.curvLe_all`; its input is the *model* statement
  `hmodels` — for every point of `M̂`, a chart model `G` agreeing with the chart metric near the
  point and having non-positive curvature there, i.e. exactly the two facts
  `Work.Space.ModelAtlas.chartGram_eq_model` and the model computations of `Curvature` Part 1
  (`Work.Curvature.secNonposAt_uhs/warped/flat`) that the `RTData` provider knows about its own
  models.

The remaining fields of `FinalInputs` (after these three discharges) are
`rt` (SPACE), `cov_smooth` (LEVICIVITA), `eM`, `eN` (DELTAHOMOLOGY/CERTIFICATES) and `hsq`
(CERTIFICATES); see `NOTES_FINAL.md`.
-/
import Submission.Work.Final.Basic
import Submission.Work.Final.MhatCover
import Submission.Work.Final.mvRightX_zero_surjective
import Submission.Work.Final.secNonpos_of_chartModels

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
set_option maxHeartbeats 4000000

open LeanEval.Topology
open CategoryTheory AlgebraicTopology
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace Work.Final

open Work.Space

noncomputable section

namespace FinalInputs

variable [D : FinalInputs]

/-- **The degree-`0` Mayer–Vietoris input for the cover of `M̂`**, discharged by
`Work.Final.mvRightX_zero_surjective`. -/
theorem mhatMVExactDegreeZero :
    MVExactDegreeZero (X := TopCat.of D.rt.Mhat) (mhatAset (rt := D.rt))
      (mhatBset (rt := D.rt)) :=
  mvExactDegreeZero_of_mvRightX (X := TopCat.of D.rt.Mhat) (mhatAset (rt := D.rt))
    (mhatBset (rt := D.rt)) (mhatAset_isOpen (rt := D.rt)) (mhatBset_isOpen (rt := D.rt))
    (mhatAset_union_mhatBset (rt := D.rt))
    (mvRightX_zero_surjective (X := TopCat.of D.rt.Mhat) (mhatAset (rt := D.rt))
      (mhatBset (rt := D.rt)) (mhatAset_isOpen (rt := D.rt)) (mhatBset_isOpen (rt := D.rt))
      (mhatAset_union_mhatBset (rt := D.rt)))

/-- **The field `L` of `FinalInputs`, discharged**: the Mayer–Vietoris long exact sequence of the
cover `M̂ = A ∪ B`, with no remaining input. -/
def mhatLES : Work.HomologyMV.MVLES :=
  mhatMVLES (rt := D.rt) (mhatMVExactDegreeZero (D := D))

/-- **The field `hX` of `FinalInputs`, discharged**: the `(k,2)`-slot of `mhatLES` is the singular
homology of `M̂`. -/
def mhatLES_hX (k : ℕ) :
    (mhatLES (D := D)).H ((k : ℤ), 2) ≅
      LeanEval.Topology.intHomology k (TopCat.of D.rt.Mhat) :=
  mhatMVLES_hX (rt := D.rt) (mhatMVExactDegreeZero (D := D)) k

/-! ## The curvature field

The field `curvLe` of `FinalInputs` is `Work.Final.secNonpos_of_chartModels` applied pointwise
(composed with `Work.CartanHadamard.curvLe_all`); the packaged statement is
`Work.Final.curvLe_of_models` below, whose proof is the composition

```
CH.curvLe_all (fun x u v hu hv huv => secNonpos_of_chartModels x (hsec x) (hmod x) u v hu hv huv)
```

with `hsec`/`hmod` the two components of the model datum `hmodels`.  The statement is delegated to
`Submission/Work/Final/curvLe_of_models.lean`: the only difficulty is that the instance arguments
of `curvVec` are synthesised from the `ChartedRiem` hypothesis in `secNonpos_of_chartModels` and
from the ambient `RiemannianBundle` instance in the goal, so a `convert` with an equality of those
instances is needed. -/

end FinalInputs

end

end Work.Final
