import Submission.Work.PinchCounted.Main
import Submission.Work.BoxShrink.Pinch.SphereTraceEssential
import Submission.Work.BoxShrink.Bubble.cex_not_slicePushOffSpan

/-!
# Negative results: what the two endpoint hypotheses cannot give

This module records, in the vocabulary of this chapter, the two facts that *force* the counted form
of Pardon's Lemma 3 to carry more than the two endpoint hypotheses
`¬ ContainsEssentialLoop (sphereSet c σ s)` and `¬ ContainsEssentialLoop (sliceRegion P s c σ u)`.

## 1. The endpoint hypotheses do not give the span form

At the standard torus of revolution with `s = 5/2`, `c = 0`, `σ = Equiv.swap 1 2`, `u = 0`:

* the sphere trace carries no essential loop
  (`Work.BoxShrink.Bubble.cex_not_containsEssentialLoop_sphereSet`);
* the slice carries no essential loop (`Work.BoxShrink.Bubble.cex_not_containsEssentialLoop_sliceRegion`);
* Pardon's Lemma 3 *conclusion* holds (`Work.BoxShrink.Bubble.bubbleHalf_cex`);
* but the **span bound** `W(boxRegion) ≤ W(upperRegion ∪ lowerRegion)` **fails**
  (`Work.BoxShrink.Bubble.cex_not_slicePushOffSpan`).

Hence `Work.BoxShrink.Bubble.SlicePushOffSpan` is not a consequence of the two endpoint hypotheses,
and neither is `CountedSpanPushOff` (whose *hypotheses* are stronger than the endpoint ones, so an
endpoint-only proof is impossible), nor is a `PinchSweep` — the span-preserving pinch — available
in the endpoint-only setting (`not_endpointOnly_pinchSweep`).  This is the precise sense in which the
count is needed: it must enter through the *intermediate* spheres, making every changed piece
inessential (`Counting.windingSpan_eq_bot_of_subset_of_count`).

## 2. The workshop's counterexample does *not* refute `SmoothHalfS`

`Work.BoxShrink.Pinch.BubbleHalfRefuted` shows that Pardon's Lemma 3 conclusion fails at the
standard torus with the **small** box `s = 3/2`, `c = 0`, `σ = swap 1 2`, `u = 0`.  At that
configuration the sphere trace is **essential**
(`Work.BoxShrink.Pinch.sphereSet_threeHalves_essential`: the curve
`θ ↦ torusMap θ (tracePhi θ)` lies in `sphereSet 0 (swap 1 2) (3/2)` and has winding `(1,0)`), so the
first endpoint hypothesis of `SmoothHalfS` *fails* there: the configuration is not a counterexample
to `SmoothHalfS`, and `SmoothHalfS` remains unrefuted.  What is refuted at scale is the span form
(§1).  The correct statement of the difficulty is therefore:

* the *conclusion* `BubbleHalf` needs the pinch (and hence, in the counted setting, the intermediate
  counts);
* the *span* form is false even with both endpoint hypotheses — a strictly stronger conclusion than
  the challenge needs.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.PinchCounted

noncomputable section

/-- **The two endpoint hypotheses do not give the span form.**  There is a configuration (the
standard torus, `s = 5/2`, `u = 0`, `σ = swap 1 2`) at which the sphere trace and the slice both carry
no essential loop, but the winding span of the box region is not contained in that of the two
half-regions. -/
theorem not_endpointOnly_slicePushOffSpan :
    ¬ (∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
        ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s) →
        ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u) →
        Work.BoxShrink.Bubble.SlicePushOffSpan P s c σ u) := by
  intro h
  exact Work.BoxShrink.Bubble.cex_not_slicePushOffSpan
    (h Work.CoreTopology.standard (5 / 2) 0 (Equiv.swap (1 : Fin 3) 2) 0
      Work.BoxShrink.Bubble.cex_not_containsEssentialLoop_sphereSet
      Work.BoxShrink.Bubble.cex_not_containsEssentialLoop_sliceRegion)

/-- **The two endpoint hypotheses do not give Pardon's pinch with span-preserving local models.**
At the same configuration, no `PinchSweep` exists, since a `PinchSweep` gives the span bound
(`PinchSweep.windingSpan_boxRegion_eq` and `SlicePushOffSpan`). -/
theorem not_endpointOnly_pinchSweep :
    ¬ (∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
        ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s) →
        ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u) →
        Nonempty (PinchSweep P s c σ u)) := by
  intro h
  obtain ⟨D⟩ := h Work.CoreTopology.standard (5 / 2) 0 (Equiv.swap (1 : Fin 3) 2) 0
    Work.BoxShrink.Bubble.cex_not_containsEssentialLoop_sphereSet
    Work.BoxShrink.Bubble.cex_not_containsEssentialLoop_sliceRegion
  exact Work.BoxShrink.Bubble.cex_not_slicePushOffSpan
    (le_of_eq (PinchSweep.windingSpan_boxRegion_eq D))

/-- **The counterexample to Pardon's Lemma 3 conclusion is not a counterexample to `SmoothHalfS`**:
at the standard torus with the small box `s = 3/2`, `u = 0`, the sphere trace *is* essential, so the
first hypothesis of `SmoothHalfS` fails there.  (Recorded because the configuration is the workshop's
witness for the falsity of the `hZ`-only interfaces `Work.BoxShrink.Bubble.SmoothHalf` and
`Work.BoxShrink.Pinch.PinchInput`; it does not touch `SmoothHalfS` or `CountingHalf`.) -/
theorem threeHalves_witness :
    Work.CoreTopology.standard.ContainsEssentialLoop
        (Work.BoxShrink.Core.sphereSet 0 (Equiv.swap 1 2) (3 / 2)) ∧
      ¬ Work.BoxShrink.Bubble.BubbleHalf Work.CoreTopology.standard (3 / 2) 0 (Equiv.swap 1 2) 0 :=
  ⟨Work.BoxShrink.Pinch.sphereSet_threeHalves_essential, Work.BoxShrink.Pinch.BubbleHalfRefuted⟩

/-- **At the `5/2` configuration the conclusion of Pardon's Lemma 3 does hold**, although the span
form fails — so the counterexample to the span form is not a counterexample to the challenge's
interface. -/
theorem fiveHalves_conclusion :
    Work.BoxShrink.Bubble.BubbleHalf Work.CoreTopology.standard (5 / 2) 0 (Equiv.swap (1 : Fin 3) 2) 0 :=
  Work.BoxShrink.Bubble.bubbleHalf_cex

/-- **The counted residuals are not vacuous**: their conclusions fail at an explicit
configuration, so no residual of this chapter (nor `CountingHalf`) is provable from `True`. -/
theorem residuals_are_falsifiable :
    ¬ Work.BoxShrink.Bubble.SlicePushOffSpan Work.CoreTopology.standard (5 / 2) 0
        (Equiv.swap (1 : Fin 3) 2) 0 :=
  Work.BoxShrink.Bubble.cex_not_slicePushOffSpan

end

end Work.PinchCounted
