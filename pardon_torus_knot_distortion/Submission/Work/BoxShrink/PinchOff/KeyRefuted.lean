import Submission.Work.BoxShrink.PinchOff.Basic
import Submission.Work.BoxShrink.PinchOff.TangentConfig

/-!
# The interface of the area is refuted: `Key`, `KeyCase`, `SmoothHalfS` and `PardonPinchInput`
are all false

`tangent_trace_counterexample_data` (delegated, axiom-clean) verifies, at the **standard** torus
with the box centre `c = (1, 0, 0)` (the inner-equator point at which the plane `{x = 1}` is
*tangent* to the surface), `s = 13/10`, `σ = (0 1 2)` and `u = 0`:

* the box sphere carries no essential loop (`hS`),
* `WindingSpan (sliceRegion …) = ⊥` (`hZ`),
* `WindingSpan (boxRegion …) = ⊤`,
* `WindingSpan (upperRegion … ∪ lowerRegion …) = ⊥`.

Consequently the box region carries an essential loop while *both* half-regions are inessential:
Pardon's Lemma 3 conclusion `BubbleHalf`, the residual `Key` (equivalently the parent chapter's
`PinchNoJump` / `PinchLemma3.SliceWall`), `SmoothHalfS` — the field `bubble` that
`Submission.lean`'s `FinalInput` asks for in its abstract form — and the library's own isolated
input `Work.BoxShrink.Bubble.PardonPinchInput` **all fail** at a configuration satisfying *both*
of the endpoint hypotheses of the area.  The same data refutes `KeyCase` and `PushOffHalf`.

**What this means for the area.**  The two endpoint hypotheses `hS`/`hZ` are *not* enough: the
missing hypothesis is the **general position of the cutting plane** — at this configuration the
plane is tangent to the surface at the inner-equator point `(1,0,0)`, and the two generators of the
box region (the meridian `{u = 0}` and the innermost longitude `{v = π}`) both meet the plane at
that tangency point, so that the plane cuts the box region into two halves which are each
inessential while the slice trace degenerates to a wedge of two arcs.  This is exactly the
hypothesis Pardon's counting argument supplies (`TransverseSlice` *inside the box*, i.e.
`TameSlice`, or the global `TransverseTrace`).  The honest residual is therefore a *conditional*
form: the parent chapter's `TraceMultipleTame` (with `TransverseSlice`/`TameSlice`), or the same
with the global `TransverseTrace`; a proof of either, plus Pardon's equation (1) and the general
position of the box-sphere trace, is what remains.  The other disjunct of the ledger
(`Work.BoxShrink.Pinch.CountingHalf`) is untouched: it carries Pardon's counting hypotheses, which
rule this configuration out.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

/-! ## The tangent configuration

The configuration itself — the identity diffeomorphism, the two hypotheses `tangent_hS`/`tangent_hZ`
at it, and the two winding spans `tangent_boxSpan_eq_top`/`tangent_halvesSpan_eq_bot` — is in
`Submission.Work.BoxShrink.PinchOff.TangentConfig`, whose content is exactly the delegated data
`tangent_trace_counterexample_data` read in the vocabulary of this chapter. -/

/-! ## The refutations -/

/-- **`Key` is false**: at the tangent configuration the box region carries an essential loop
while both half-regions are inessential, so the one-sided dimension bound reads `2 ≤ 0 + 1`. -/
theorem not_key : ¬ Key := by
  intro h
  have hb := h idDiffeo tangentRad tangentCtr tangentCyc3 0 tangent_hS tangent_hZ
  rw [tangent_boxSpan_eq_top, tangent_halvesSpan_eq_bot] at hb
  have h2 : Module.finrank ℚ ↥(⊤ : Submodule ℚ (ℚ × ℚ)) = 2 := by
    rw [finrank_top, Module.finrank_prod]
    simp
  have h0 : Module.finrank ℚ ↥(⊥ : Submodule ℚ (ℚ × ℚ)) = 0 := by rw [finrank_bot]
  rw [h2, h0] at hb
  omega

/-- **`KeyCase` is false** (it is equivalent to `Key` by `key_iff_keyCase`). -/
theorem not_keyCase : ¬ KeyCase := fun h => not_key (key_iff_keyCase.mpr h)

/-- **The parent chapter's `PinchNoJump` is false** (`Key` *is* it, definitionally). -/
theorem not_pinchNoJump : ¬ Work.BoxShrink.Pinch.PinchNoJump := fun h => not_key h

-- (The sibling chapter `Work.PinchLemma3` states the same residual as `SliceWall` and proves
-- `Work.PinchLemma3.sliceWall_iff_pinchNoJump : SliceWall ↔ PinchNoJump`; that chapter imports
-- *this* directory, so `SliceWall` cannot be named here.  Via that equivalence, `not_pinchNoJump`
-- above refutes `Work.PinchLemma3.SliceWall` as well.)

/-- **The deliverable's field `BubbleHalf` fails at the tangent configuration**: the box region
carries an essential loop while neither half-region does. -/
theorem not_bubbleHalf_tangent :
    ¬ Work.BoxShrink.Bubble.BubbleHalf Work.CoreTopology.standard tangentRad tangentCtr
      tangentCyc3 0 := by
  intro hb
  have hbox : Work.CoreTopology.standard.ContainsEssentialLoop
      (Work.BoxShrink.Core.boxRegion Work.CoreTopology.standard tangentRad tangentCtr
        tangentCyc3) :=
    (Work.SurgeryInvariance.windingSpan_ne_bot_iff _ _).mp
      (by rw [tangent_boxRegion_span_eq_top]; exact top_ne_bot)
  rcases hb hbox with hup | hlo
  · have hle := Work.SurgeryInvariance.WindingSpan_mono Work.CoreTopology.standard
      (show Work.BoxShrink.Core.upperRegion Work.CoreTopology.standard tangentRad tangentCtr
          tangentCyc3 0 ⊆
        (Work.BoxShrink.Core.upperRegion Work.CoreTopology.standard tangentRad tangentCtr
            tangentCyc3 0 ∪
          Work.BoxShrink.Core.lowerRegion Work.CoreTopology.standard tangentRad tangentCtr
            tangentCyc3 0) from Set.subset_union_left)
    have hbot : Work.SurgeryInvariance.WindingSpan Work.CoreTopology.standard
        (Work.BoxShrink.Core.upperRegion Work.CoreTopology.standard tangentRad tangentCtr
          tangentCyc3 0) = ⊥ :=
      le_bot_iff.mp (hle.trans (le_of_eq tangent_halfRegions_span_eq_bot))
    exact (Work.SurgeryInvariance.WindingSpan_eq_bot_iff _ _).mp hbot hup
  · have hle := Work.SurgeryInvariance.WindingSpan_mono Work.CoreTopology.standard
      (show Work.BoxShrink.Core.lowerRegion Work.CoreTopology.standard tangentRad tangentCtr
          tangentCyc3 0 ⊆
        (Work.BoxShrink.Core.upperRegion Work.CoreTopology.standard tangentRad tangentCtr
            tangentCyc3 0 ∪
          Work.BoxShrink.Core.lowerRegion Work.CoreTopology.standard tangentRad tangentCtr
            tangentCyc3 0) from Set.subset_union_right)
    have hbot : Work.SurgeryInvariance.WindingSpan Work.CoreTopology.standard
        (Work.BoxShrink.Core.lowerRegion Work.CoreTopology.standard tangentRad tangentCtr
          tangentCyc3 0) = ⊥ :=
      le_bot_iff.mp (hle.trans (le_of_eq tangent_halfRegions_span_eq_bot))
    exact (Work.SurgeryInvariance.WindingSpan_eq_bot_iff _ _).mp hbot hlo

/-- **`PushOffHalf` is false**: it is the `∀ P` form of `BubbleHalf`, refuted at the tangent
configuration. -/
theorem not_pushOffHalf : ¬ Work.BoxShrink.Bubble.PushOffHalf := fun h =>
  not_bubbleHalf_tangent (h Work.CoreTopology.standard tangentRad tangentCtr tangentCyc3 0
    tangent_hS tangent_hZ)

/-- **Pardon's Lemma 3 conclusion with both endpoint hypotheses is false**:
`SmoothHalfS` is refuted at the tangent configuration, so the field `bubble` of `Submission.lean`'s
`FinalInput` cannot be inhabited in this abstract form. -/
theorem not_smoothHalfS : ¬ Work.BoxShrink.Pinch.SmoothHalfS := by
  intro h
  have hb := h idDiffeo tangentRad tangentCtr tangentCyc3 0 tangent_hS tangent_hZ
  exact not_bubbleHalf_tangent hb

/-- **The library's isolated input `Work.BoxShrink.Bubble.PardonPinchInput` is false**: it would
give `PushOffHalf` (`Work.BoxShrink.Bubble.pushOffHalf_of_pardonPinchInput`). -/
theorem not_pardonPinchInput : Work.BoxShrink.Bubble.PardonPinchInput → False := fun h =>
  not_pushOffHalf (Work.BoxShrink.Bubble.pushOffHalf_of_pardonPinchInput h)

/-- **The assignment's target is unprovable in the form stated**: the residual of the pinch
cannot be inhabited under the two endpoint hypotheses alone, because its consequence
`Work.BoxShrink.Pinch.SmoothHalfS` — and with it `BubbleHalf` — fails at the tangent configuration
of the standard torus. -/
theorem not_key_and_not_pardonPinchInput :
    ¬ Key ∧ (Work.BoxShrink.Bubble.PardonPinchInput → False) :=
  ⟨not_key, not_pardonPinchInput⟩

end

end Work.BoxShrink.PinchOff
