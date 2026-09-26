import Submission.Work.BoxShrink.PinchOff.Basic
import Submission.Work.BoxShrink.PinchOff.tangent_trace_counterexample_data

/-!
# The tangent configuration of the standard torus, in the vocabulary of this chapter

The standard torus with the box centre `c = (1,0,0)` — the inner-equator point where the plane
`{x = 1}` is tangent to the surface — the box radius `s = 13/10`, the cyclic permutation
`σ = (0 1 2)` and the cutting plane `{x = 1}` (`u = 0`).  This module collects, in the vocabulary of
this chapter, the four facts about it that the refutation `KeyRefuted.lean` consumes, and the
identity diffeomorphism of `ℝ³` (whose surface is the standard torus, definitionally) through which
the chapter's statements are instantiated at it.

All four facts are the delegated, axiom-clean lemmas of
`Submission.Work.BoxShrink.PinchOff.tangent_trace_counterexample_data` (`TangentData/Basic.lean`
and the four `tangent_*` modules beside it):

* `tangent_hS` — the box sphere carries no essential loop;
* `tangent_sliceSpan_eq_bot`, `tangent_hZ` — the slice carries none;
* `tangent_boxSpan_eq_top` — the box region spans the whole of `H₁`;
* `tangent_halvesSpan_eq_bot` — the two half-regions span nothing.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

/-! ## The identity diffeomorphism of `ℝ³` -/

/-- The identity diffeomorphism. -/
def idDiffeo : Submission.Diffeo where
  toFun := id
  invFun := id
  smooth_toFun := contDiff_id
  smooth_invFun := contDiff_id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- The surface of `idDiffeo` is the standard torus (definitionally). -/
theorem surface_idDiffeo_eq_standard : surface idDiffeo = Work.CoreTopology.standard := rfl

/-- **`hS` at the tangent configuration**: the box sphere carries no essential loop. -/
theorem tangent_hS :
    ¬ Work.CoreTopology.standard.ContainsEssentialLoop
      (Work.BoxShrink.Core.sphereSet tangentCtr tangentCyc3 tangentRad) :=
  tangent_trace_counterexample_data.1

/-- The slice of the tangent configuration has vanishing winding span. -/
theorem tangent_sliceSpan_eq_bot :
    Work.SurgeryInvariance.WindingSpan Work.CoreTopology.standard
      (Work.BoxShrink.Core.sliceRegion Work.CoreTopology.standard tangentRad tangentCtr
        tangentCyc3 0) = ⊥ :=
  tangent_trace_counterexample_data.2.1

/-- **`hZ` at the tangent configuration**: the slice carries no essential loop. -/
theorem tangent_hZ :
    ¬ Work.CoreTopology.standard.ContainsEssentialLoop
      (Work.BoxShrink.Core.sliceRegion Work.CoreTopology.standard tangentRad tangentCtr
        tangentCyc3 0) :=
  (Work.SurgeryInvariance.WindingSpan_eq_bot_iff _ _).mp tangent_sliceSpan_eq_bot

/-- The box region of the tangent configuration, in the vocabulary of this chapter. -/
theorem tangent_boxSpan_eq_top :
    Work.SurgeryInvariance.WindingSpan (surface idDiffeo)
      (Omega idDiffeo tangentRad tangentCtr tangentCyc3) = ⊤ :=
  tangent_trace_counterexample_data.2.2.1

/-- The two half-regions of the tangent configuration, in the vocabulary of this chapter. -/
theorem tangent_halvesSpan_eq_bot :
    Work.SurgeryInvariance.WindingSpan (surface idDiffeo)
      (Halves idDiffeo tangentRad tangentCtr tangentCyc3 0) = ⊥ :=
  tangent_trace_counterexample_data.2.2.2

/-- The box region of the tangent configuration, in the vocabulary of the parent chapter. -/
theorem tangent_boxRegion_span_eq_top :
    Work.SurgeryInvariance.WindingSpan Work.CoreTopology.standard
      (Work.BoxShrink.Core.boxRegion Work.CoreTopology.standard tangentRad tangentCtr
        tangentCyc3) = ⊤ :=
  tangent_trace_counterexample_data.2.2.1

/-- The two half-regions of the tangent configuration, in the vocabulary of the parent chapter.
(The parent chapter's `halfRegions` is *defined* as this union, so the two statements are the
same.) -/
theorem tangent_halfRegions_span_eq_bot :
    Work.SurgeryInvariance.WindingSpan Work.CoreTopology.standard
      (Work.BoxShrink.Core.upperRegion Work.CoreTopology.standard tangentRad tangentCtr
          tangentCyc3 0 ∪
        Work.BoxShrink.Core.lowerRegion Work.CoreTopology.standard tangentRad tangentCtr
          tangentCyc3 0) = ⊥ :=
  tangent_trace_counterexample_data.2.2.2

end

end Work.BoxShrink.PinchOff
