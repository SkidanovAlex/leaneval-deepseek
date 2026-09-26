import Submission.Work.BoxShrink.Bubble.Disc
import Submission.Work.BoxShrink.Bubble.Sweep.exists_sweepLoops_of_surgeryStepZero

/-!
# The case in which the slice is open: the decomposition *is* a `2`-surgery

`Work.BoxShrink.Core.boxRegion_eq_union` writes the region inside the box as

  `boxRegion = (upperRegion ∪ lowerRegion) ∪ sliceRegion`,

with `upperRegion`, `lowerRegion` open in the surface and disjoint from the closed slice.  The
naive hope — that this *is* one `2`-surgery, so that the double-bubble family consists of a single
step — is exactly the hope that the closed piece `sliceRegion` is open in the surface (a
`SurgeryStepZero` requires the changed piece to be open in the carrier).  That fails in general
(`Obstruction.lean`), but when it holds the family exists with **no extra geometry at all**:

* `surgeryStepZero_boxRegion_of_sliceOpen`: if the slice is open in the surface, then
  `SurgeryStepZero P (boxRegion) (upperRegion ∪ lowerRegion)` holds, with the changed piece
  `sliceRegion`, whose winding span is `⊥` exactly by the hypothesis
  `¬ P.ContainsEssentialLoop (sliceRegion)` (Pardon's plane count);
* `bubbleSweep_of_sliceOpen`: consequently the double-bubble family exists, by the single-step
  sweep of `Work.BoxShrink.Bubble.Sweep.exists_sweepLoops_of_surgeryStepZero`.

This is the sharpest form of the *obstruction* documented in `README.md`: the whole content of
Pardon's pinch is the failure of the slice to be open in the surface — the slice has to be
*fattened* inside the surface (a collar), and the fattened piece has to be produced by the double
bubble itself.

Instances in which the slice *is* open in the surface: the surface contains an open patch of the
cutting plane (a flat piece of the torus); then `sliceRegion` is the intersection of that patch
with the box.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Bubble

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-- **If the slice is open in the surface, the decomposition of the region is a single
`2`-surgery.** -/
theorem surgeryStepZero_boxRegion_of_sliceOpen {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hopen : Work.SurgeryInvariance.IsOpenInCarrier P (Work.BoxShrink.Core.sliceRegion P s c σ u))
    (hZ : ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u)) :
    Work.SurgeryInvariance.SurgeryStepZero P (Work.BoxShrink.Core.boxRegion P s c σ)
      (Work.BoxShrink.Core.upperRegion P s c σ u ∪
        Work.BoxShrink.Core.lowerRegion P s c σ u) := by
  refine ⟨Work.BoxShrink.Core.sliceRegion P s c σ u,
    (Work.SurgeryInvariance.WindingSpan_eq_bot_iff P _).mpr hZ,
    Work.BoxShrink.Core.isOpenInCarrier_boxRegion P s c σ, ?_, hopen, ?_⟩
  · exact Work.SurgeryInvariance.isOpenInCarrier_union P
      (Work.BoxShrink.Core.isOpenInCarrier_upperRegion P s c σ u)
      (Work.BoxShrink.Core.isOpenInCarrier_lowerRegion P s c σ u)
  · exact Or.inl ⟨Work.BoxShrink.Core.boxRegion_eq_union P s c σ u,
      (Work.BoxShrink.Bubble.disjoint_sliceRegion_upper_union_lower P s c σ u).symm⟩

/-- **The double-bubble family when the slice is open in the surface.** -/
theorem nonempty_bubbleSweep_of_sliceOpen {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hopen : Work.SurgeryInvariance.IsOpenInCarrier P (Work.BoxShrink.Core.sliceRegion P s c σ u))
    (hZ : ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u)) :
    Nonempty (Work.BoxShrink.Core.BubbleSweep P s c σ u) := by
  obtain ⟨S, h0, h1⟩ := Sweep.exists_sweepLoops_of_surgeryStepZero
    (surgeryStepZero_boxRegion_of_sliceOpen (P := P) hopen hZ)
  exact ⟨{ sweep := S, zero := h0, one := h1 }⟩

/-- **The field `bubble`, in the case of an open slice.** -/
noncomputable def bubbleSweep_of_sliceOpen {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hopen : Work.SurgeryInvariance.IsOpenInCarrier P (Work.BoxShrink.Core.sliceRegion P s c σ u))
    (hZ : ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u)) :
    Work.BoxShrink.Core.BubbleSweep P s c σ u :=
  Classical.choice (nonempty_bubbleSweep_of_sliceOpen (P := P) hopen hZ)

/-- **The field, from openness of the slice for every configuration.** -/
noncomputable def bubble_of_sliceOpenAll
    (hopen : ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
      (u : ℝ), Work.SurgeryInvariance.IsOpenInCarrier P
        (Work.BoxShrink.Core.sliceRegion P s c σ u)) :
    ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s) →
      ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u) →
      Work.BoxShrink.Core.BubbleSweep P s c σ u :=
  fun P s c σ u _ hZ => bubbleSweep_of_sliceOpen (P := P) (hopen P s c σ u) hZ

end

end Work.BoxShrink.Bubble
