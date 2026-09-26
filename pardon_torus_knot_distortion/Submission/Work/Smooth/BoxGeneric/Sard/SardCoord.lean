import Mathlib
import Submission.Work.Smooth.BoxGeneric.Sard.Reduce
import Submission.Work.Smooth.BoxGeneric.Sard.criticalValues_null_of_contDiffTwo_periodic

/-!
# `SardCoord` holds unconditionally

Two-dimensional Sard for `C²` functions on the plane
(`Work.Smooth.BoxGeneric.Sard.criticalValues_null_of_contDiffTwo_periodic`, proved from the
one-dimensional Sard lemma of Mathlib plus a covering argument) makes the Sard input of the
chapter `Work.Smooth.BoxGeneric.SardCoord` a *theorem*: almost every level of every coordinate
function on the smooth surface `F = ψ(standard torus)` is a regular value.

Consequently none of the main results of the chapter needs the smoothness input; what remains are
the genericity of the corner and vertex strata (`AeTransverseCorner`, `AeNoVertex`), the
classification of compact `1`-manifolds and the classical Jordan–Schoenflies slicing input.
-/

open LeanEval.KnotTheory.PardonDistortion

namespace Work.Smooth.BoxGeneric.Sard

noncomputable section

/-- **Sard for the coordinate functions on the surface, unconditionally.** -/
theorem sardCoord (ψ : Submission.Diffeo) : Work.Smooth.BoxGeneric.SardCoord ψ :=
  sardCoord_of_criticalValues_null ψ fun i =>
    criticalValues_null_of_contDiffTwo_periodic
      ((pullback_coord_contDiff ψ i).of_le (WithTop.coe_le_coe.mpr le_top))
      (pullback_coord_periodic_left ψ i) (pullback_coord_periodic_right ψ i)

end

end Work.Smooth.BoxGeneric.Sard
