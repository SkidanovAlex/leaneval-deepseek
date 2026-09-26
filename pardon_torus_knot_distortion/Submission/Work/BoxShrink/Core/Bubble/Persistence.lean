import Submission.Work.BoxShrink.Core.Bubble.Defs

/-!
# Pardon's double bubble: the persistence of the essential loop

This file draws the consequence of the local-model datum `BubbleSweep` that Pardon's shrinking step
consumes: the essential loop of `F` inside the sphere `∂PBox s c σ` survives, along the family of
the double bubble, to the union of the two half-regions, and since the two half-regions are open and
disjoint, it survives to one of them.

The two steps are

* `windingSpan_eq_of_bubbleSweep` — the winding span of the region is constant along the family
  (`Work.SurgeryInvariance.SweepLoops.windingSpan_eq`, applied at the two endpoints of the
  `BubbleSweep`);
* `containsEssentialLoop_half_of_bubbleSweep` — the region `upperRegion ∪ lowerRegion` is the
  disjoint union of two open pieces of the surface, so its winding span is the supremum of theirs
  (`Work.SurgeryInvariance.Span.union_eq_sup`), and a nonzero supremum has a nonzero summand.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Core

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-- **The winding span is constant along the double bubble.**  The region inside the sphere and the
union of the two half-regions cut out by the plane have the same winding span: this is Pardon's
`spherefamily` applied to the family of spheres which pinches the box boundary along the slicing
disc. -/
theorem windingSpan_eq_of_bubbleSweep {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (B : BubbleSweep P s c σ u) :
    Work.SurgeryInvariance.WindingSpan P (boxRegion P s c σ) =
      Work.SurgeryInvariance.WindingSpan P
        (upperRegion P s c σ u ∪ lowerRegion P s c σ u) := by
  have h := B.sweep.windingSpan_eq 1
  rw [B.zero] at h
  rw [B.one] at h
  exact h.symm

/-- **The essential loop survives to one of the two halves.**

If the region of the surface inside the sphere `∂PBox s c σ` contains an essential loop, then so
does the union of the two half-regions cut out by the plane `{y (σ 2) = c (σ 2) + u}`; the union is
the disjoint union of two pieces which are open in the surface, so one of the two pieces must carry
the loop.

This is Pardon's Lemma 3 (`doublebubble`) in the form in which the shrinking step consumes it. -/
theorem containsEssentialLoop_half_of_bubbleSweep {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    {u : ℝ} (B : BubbleSweep P s c σ u) (h : P.ContainsEssentialLoop (boxRegion P s c σ)) :
    P.ContainsEssentialLoop (upperRegion P s c σ u) ∨
      P.ContainsEssentialLoop (lowerRegion P s c σ u) := by
  have h0 : P.ContainsEssentialLoop (B.sweep.region 0) := by
    rw [B.zero]; exact h
  have h1 : P.ContainsEssentialLoop (B.sweep.region 1) := B.sweep.spherefamily h0
  rw [B.one] at h1
  have hsplit := Work.SurgeryInvariance.Span.union_eq_sup (P := P)
    (isOpenInCarrier_upperRegion P s c σ u) (isOpenInCarrier_lowerRegion P s c σ u)
    (disjoint_upperRegion_lowerRegion P s c σ u)
  have hne : Work.SurgeryInvariance.WindingSpan P (upperRegion P s c σ u) ⊔
      Work.SurgeryInvariance.WindingSpan P (lowerRegion P s c σ u) ≠ ⊥ := by
    rw [← hsplit]
    exact (Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mpr h1
  rcases not_and_or.mp (fun hh : Work.SurgeryInvariance.WindingSpan P (upperRegion P s c σ u) = ⊥ ∧
      Work.SurgeryInvariance.WindingSpan P (lowerRegion P s c σ u) = ⊥ =>
    hne (by rw [hh.1, hh.2, sup_bot_eq])) with hup | hlo
  · exact Or.inl ((Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mp hup)
  · exact Or.inr ((Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mp hlo)

end

end Work.BoxShrink.Core
