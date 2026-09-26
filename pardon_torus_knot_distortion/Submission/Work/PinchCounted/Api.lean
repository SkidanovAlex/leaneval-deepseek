import Submission.Work.PinchCounted.Instances

/-!
# The interface of the chapter

Small API lemmas around `Work.PinchCounted.PinchSweep`:
the equivalence of Pardon's Lemma 3 conclusion with the non-vanishing of the span of the two
half-regions, the two halves of the span, and the trivial instances of the pinch in the degenerate
geometries (empty slice, box region inessential).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.PinchCounted

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-- **The two half-regions carry an essential loop iff one of them does** (they are open and
disjoint in the surface). -/
theorem halves_containsEssentialLoop_iff (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    P.ContainsEssentialLoop (PinchSweep.halves P s c σ u) ↔
      P.ContainsEssentialLoop (Work.BoxShrink.Core.upperRegion P s c σ u) ∨
        P.ContainsEssentialLoop (Work.BoxShrink.Core.lowerRegion P s c σ u) := by
  rw [← Work.SurgeryInvariance.windingSpan_ne_bot_iff, PinchSweep.windingSpan_halves P s c σ u,
    ← Work.SurgeryInvariance.windingSpan_ne_bot_iff, ← Work.SurgeryInvariance.windingSpan_ne_bot_iff]
  constructor
  · intro h
    rcases not_and_or.mp (fun hcon => h (sup_eq_bot_iff.mpr hcon)) with h' | h'
    · exact Or.inl h'
    · exact Or.inr h'
  · rintro (h | h) hcon
    · exact h ((sup_eq_bot_iff.mp hcon).1)
    · exact h ((sup_eq_bot_iff.mp hcon).2)

/-- **Pardon's Lemma 3 conclusion in the vocabulary of this chapter**: the conclusion holds iff
an essential loop of the region inside the box survives to the two half-regions together. -/
theorem bubbleHalf_iff (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Work.BoxShrink.Bubble.BubbleHalf P s c σ u ↔
      (P.ContainsEssentialLoop (Work.BoxShrink.Core.boxRegion P s c σ) →
        P.ContainsEssentialLoop (PinchSweep.halves P s c σ u)) := by
  constructor
  · intro h hbox
    exact (halves_containsEssentialLoop_iff P s c σ u).mpr (h hbox)
  · intro h hbox
    exact (halves_containsEssentialLoop_iff P s c σ u).mp (h hbox)

/-- The span form of the same: the conclusion holds iff the vanishing of the winding span is
preserved from the box region to the two half-regions. -/
theorem bubbleHalf_iff_halves_span_ne_bot (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Work.BoxShrink.Bubble.BubbleHalf P s c σ u ↔
      (Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ≠ ⊥ →
        Work.SurgeryInvariance.WindingSpan P (PinchSweep.halves P s c σ u) ≠ ⊥) := by
  rw [bubbleHalf_iff P s c σ u]
  simp only [← Work.SurgeryInvariance.windingSpan_ne_bot_iff]

/-- **The pinching family gives the span statement**: `W(boxRegion) = W(halves)`, so in particular
one of the two half-regions carries an essential loop as soon as the box region does. -/
theorem spanPushOffSpan_of_pinchSweep {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (D : PinchSweep P s c σ u) :
    Work.BoxShrink.Bubble.SlicePushOffSpan P s c σ u :=
  le_of_eq (D.windingSpan_boxRegion_eq)

/-- **The pinch when the slice is empty**: the box region already is the union of the two
half-regions, so the constant family with `Z = ∅` is Pardon's pinch. -/
theorem pinchSweep_of_sliceRegion_empty {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : Work.BoxShrink.Core.sliceRegion P s c σ u = ∅) : Nonempty (PinchSweep P s c σ u) :=
  ⟨pinchSweepOfHalvesEqBoxRegion (P := P)
    (Work.BoxShrink.Core.boxRegion_eq_union P s c σ u ▸ by rw [h, Set.union_empty])⟩

/-- **The pinch when the box misses the surface**: the box region and the two halves are all empty,
and the constant family is Pardon's pinch. -/
theorem pinchSweep_of_boxRegion_empty {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : Work.BoxShrink.Core.boxRegion P s c σ = ∅) : Nonempty (PinchSweep P s c σ u) := by
  have hu : Work.BoxShrink.Core.upperRegion P s c σ u = ∅ :=
    Set.subset_empty_iff.mp ((Work.BoxShrink.Core.upperRegion_subset P s c σ u).trans h.le)
  have hl : Work.BoxShrink.Core.lowerRegion P s c σ u = ∅ :=
    Set.subset_empty_iff.mp ((Work.BoxShrink.Core.lowerRegion_subset P s c σ u).trans h.le)
  refine ⟨pinchSweepOfHalvesEqBoxRegion (P := P) ?_⟩
  show Work.BoxShrink.Core.upperRegion P s c σ u ∪ Work.BoxShrink.Core.lowerRegion P s c σ u =
    Work.BoxShrink.Core.boxRegion P s c σ
  rw [hu, hl, Set.empty_union, h]

/-- **If the box region carries no essential loop, Pardon's Lemma 3 conclusion is trivial.** -/
theorem bubbleHalf_of_boxRegion_windingSpan_bot {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) = ⊥) :
    Work.BoxShrink.Bubble.BubbleHalf P s c σ u := by
  intro hbox
  rw [← Work.SurgeryInvariance.windingSpan_ne_bot_iff, h] at hbox
  exact absurd rfl hbox

end

end Work.PinchCounted
