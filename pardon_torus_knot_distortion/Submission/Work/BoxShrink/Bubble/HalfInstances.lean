import Submission.Work.BoxShrink.Bubble.Corrected
import Submission.Work.BoxShrink.Bubble.Instances
import Submission.Work.BoxShrink.Bubble.Equivalence
import Submission.Work.BoxShrink.Bubble.DiscRoute
import Submission.Work.BoxShrink.Bubble.Neck
import Submission.Work.BoxShrink.Bubble.Smooth
import Submission.Work.BoxShrink.Bubble.Plane.FiniteSlice
import Submission.Work.BoxShrink.Bubble.Plane.CountableSlice

/-!
# The corrected conclusion in every case in which the old input was proved

`Work.BoxShrink.Bubble.BubbleHalf` (Pardon's Lemma 3 conclusion) is implied by every sufficient
condition for the old push-off (`Work.BoxShrink.Bubble.bubbleHalf_of_slicePushOff`,
`Work.BoxShrink.Bubble.bubbleHalf_of_bubbleSweep`).  This file records the resulting *instances* of
the corrected conclusion, so that a caller can discharge `BubbleHalf` (and hence the shrinking step,
via `Work.BoxShrink.Bubble.crux_of_pushOffHalf` / `crux_of_smoothHalf`) in all the configurations in
which the chapter proves the old input:

* the degenerate cases: `bubbleHalf_of_not_hasEssBox` (the region inside the box carries no
  essential loop — the conclusion is vacuous) and `bubbleHalf_of_span_bot` (the same, from the
  vanishing of the winding span);
* `bubbleHalf_of_empty_slice`, `bubbleHalf_of_sliceOpen`;
* `bubbleHalf_of_finite_slice`, `bubbleHalf_of_countable_slice` (the plane meets the region in
  finitely many / countably many points on compacta);
* `bubbleHalf_of_discRoute` (the disc-routing local model);
* `bubbleHalf_of_neckComponent` (Pardon's neck);
* `bubbleHalf_of_belowPlateau` / `bubbleHalf_of_abovePlateau` (the region is a below- and above-plateau
  of the plane coordinate over a critical-value-free interval).

Everything else follows from the two generic implications
`Work.BoxShrink.Bubble.bubbleHalf_of_slicePushOff` and
`Work.BoxShrink.Bubble.bubbleHalf_of_bubbleSweep` (e.g. the cases of `Instances.lean`, the gauge/Sard
route of `Smooth/GaugeFlow.lean` and `Smooth/etaFlow.lean`).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Bubble

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-! ## The degenerate cases -/

/-- If the region inside the box carries no essential loop, the corrected conclusion is vacuous. -/
theorem bubbleHalf_of_not_hasEssBox {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.boxRegion P s c σ)) :
    BubbleHalf P s c σ u :=
  fun hbox => absurd hbox h

/-- If the winding span of the region inside the box vanishes, it carries no essential loop and the
corrected conclusion is vacuous (`Work.BoxShrink.Core.windingSpan_eq_bot_iff`). -/
theorem bubbleHalf_of_span_bot {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) = ⊥) :
    BubbleHalf P s c σ u :=
  bubbleHalf_of_not_hasEssBox
    ((Work.SurgeryInvariance.WindingSpan_eq_bot_iff P _).mp h)

/-! ## The geometric cases -/

/-- The corrected conclusion when the slice is empty. -/
theorem bubbleHalf_of_empty_slice {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : Work.BoxShrink.Core.sliceRegion P s c σ u = ∅) : BubbleHalf P s c σ u :=
  bubbleHalf_of_slicePushOff (Work.BoxShrink.Bubble.Instances.slicePushOff_of_empty_slice (P := P) h)

/-- The corrected conclusion when the slice is open in the surface. -/
theorem bubbleHalf_of_sliceOpen {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hopen : Work.SurgeryInvariance.IsOpenInCarrier P
      (Work.BoxShrink.Core.sliceRegion P s c σ u))
    (hZ : ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u))
    (hne : (Work.BoxShrink.Core.upperRegion P s c σ u ∪
      Work.BoxShrink.Core.lowerRegion P s c σ u).Nonempty) :
    BubbleHalf P s c σ u :=
  bubbleHalf_of_slicePushOff (slicePushOff_of_sliceOpen (P := P) hopen hZ hne)

/-- The corrected conclusion when the plane meets the region inside the box in finitely many
points. -/
theorem bubbleHalf_of_finite_slice {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hfin : (Work.BoxShrink.Core.sliceRegion P s c σ u).Finite) : BubbleHalf P s c σ u :=
  bubbleHalf_of_slicePushOff (slicePushOff_of_finite_slice (P := P) hfin)

/-- The corrected conclusion when the plane meets the region inside the box in countably many
points on compacta. -/
theorem bubbleHalf_of_countable_slice {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hcount : (Work.BoxShrink.Core.sliceRegion P s c σ u).Countable) : BubbleHalf P s c σ u :=
  bubbleHalf_of_slicePushOff (slicePushOff_of_countable_slice (P := P) hcount)

/-- The corrected conclusion from the disc-routing local model. -/
theorem bubbleHalf_of_discRoute {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    {D : Work.SurgeryInvariance.DiscRegion P}
    (hslice : Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ D.interior)
    (hDsub : D.carrier ⊆ Work.BoxShrink.Core.boxRegion P s c σ)
    (hroute : SliceDiscRoute P s c σ u D) : BubbleHalf P s c σ u :=
  bubbleHalf_of_slicePushOff (slicePushOff_of_discRoute hslice hDsub hroute)

/-- The corrected conclusion from Pardon's neck. -/
theorem bubbleHalf_of_neckComponent {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (N : NeckComponent P s c σ u) : BubbleHalf P s c σ u :=
  fun hbox => bubbleHalf_of_bubbleSweep
    ((Work.BoxShrink.Bubble.Neck.bubbleSweep_of_neckComponent N).some) hbox

/-- The corrected conclusion when the region inside the box is a below-plateau of the plane
coordinate over a critical-value-free interval containing `0`. -/
theorem bubbleHalf_of_belowPlateau {ψ : Submission.Diffeo} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u a b : ℝ}
    (hab : a ≤ b) (ha : a < 0) (hb : 0 < b)
    (hreg : ∀ t ∈ Set.Icc a b, Work.Smooth.Morse.IsRegularValue ψ (planeCoord c σ u) t)
    (hcont : ∀ x ∈ (Work.Smooth.Morse.torus ψ).carrier, planeCoord c σ u x < b →
      x ∈ Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ)
    (hbox : ∀ x ∈ Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ,
      planeCoord c σ u x < b) :
    BubbleHalf (Work.Smooth.Morse.torus ψ) s c σ u :=
  bubbleHalf_of_slicePushOff
    (slicePushOff_of_belowPlateau (ψ := ψ) hab ha hb hreg hcont hbox)

/-- The corrected conclusion when the region inside the box is an above-plateau of the plane
coordinate over a critical-value-free interval containing `0`. -/
theorem bubbleHalf_of_abovePlateau {ψ : Submission.Diffeo} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u a b : ℝ}
    (hab : a ≤ b) (ha : a < 0) (hb : 0 < b)
    (hreg : ∀ t ∈ Set.Icc (-b) (-a),
      Work.Smooth.Morse.IsRegularValue ψ (fun y : R3 => -planeCoord c σ u y) t)
    (hcont : ∀ x ∈ (Work.Smooth.Morse.torus ψ).carrier, -planeCoord c σ u x < -b →
      x ∈ Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ)
    (hbox : ∀ x ∈ Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ,
      -planeCoord c σ u x < -a) :
    BubbleHalf (Work.Smooth.Morse.torus ψ) s c σ u :=
  bubbleHalf_of_slicePushOff
    (slicePushOff_of_abovePlateau (ψ := ψ) hab ha hb hreg hcont hbox)

end

end Work.BoxShrink.Bubble
