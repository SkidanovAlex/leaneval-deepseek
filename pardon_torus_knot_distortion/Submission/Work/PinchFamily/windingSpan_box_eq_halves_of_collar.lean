import Mathlib
import Submission.Work.PinchFamily.Defs
import Submission.Work.PinchFamily.Collar
import Submission.Work.SurgeryInvariance.Span.union_eq_sup

namespace Work.PinchFamily

open LeanEval.KnotTheory.PardonDistortion
open Set

/-- **The box region is the disjoint union of the collar and its complement.**  Hence its winding
span is the supremum of the spans of the two pieces; since the collar has vanishing span, the span
of the box region is that of the complement `box \ Z`. -/
theorem windingSpan_box_eq_windingSpan_sdiff {P : Work.CoreTopology.ParamTorus} {s : ℝ}
    {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} {Z : Set R3}
    (hZ : IsPinchCollar P s c σ u Z)
    (hspan : Work.SurgeryInvariance.WindingSpan P Z = ⊥) :
    Work.SurgeryInvariance.WindingSpan P (box P s c σ) =
      Work.SurgeryInvariance.WindingSpan P (box P s c σ \ Z) := by
  have hbox := congrArg (Work.SurgeryInvariance.WindingSpan P) hZ.box_eq_union
  rw [hbox,
    Work.SurgeryInvariance.Span.union_eq_sup hZ.open_sdiff hZ.isOpen hZ.disjoint_sdiff,
    hspan, sup_bot_eq]

/-- **The two half-regions are the disjoint union of the complement of the collar and the part of
the collar lying in them.**  Hence their winding span is likewise that of the complement: the piece
of the collar contributed to the half-regions has vanishing span. -/
theorem windingSpan_halves_eq_windingSpan_sdiff {P : Work.CoreTopology.ParamTorus} {s : ℝ}
    {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} {Z : Set R3}
    (hZ : IsPinchCollar P s c σ u Z)
    (hspan : Work.SurgeryInvariance.WindingSpan P Z = ⊥) :
    Work.SurgeryInvariance.WindingSpan P (halves P s c σ u) =
      Work.SurgeryInvariance.WindingSpan P (box P s c σ \ Z) := by
  have hZspan : Work.SurgeryInvariance.WindingSpan P (halves P s c σ u ∩ Z) = ⊥ :=
    le_antisymm
      ((Work.SurgeryInvariance.WindingSpan_mono P Set.inter_subset_right).trans_eq hspan) bot_le
  rw [halves_eq_sdiff_union (P := P) hZ,
    Work.SurgeryInvariance.Span.union_eq_sup hZ.open_sdiff
      (Work.SurgeryInvariance.isOpenInCarrier_inter (P := P)
        (Work.PinchCounted.PinchSweep.isOpenInCarrier_halves P s c σ u) hZ.isOpen)
      (disjoint_sdiff_inter (P := P) hZ),
    hZspan, sup_bot_eq]

/-- **The winding span of the box region equals that of the two half-regions, given a collar of
vanishing winding span.**  Both regions are the union of the common piece `box \ Z` with a piece of
zero span: the collar `Z` itself in the first case, and the part `halves ∩ Z` of the collar in the
second.  Since the pieces are disjoint and open in the surface, the winding span of a union is the
supremum of the spans (`Work.SurgeryInvariance.Span.union_eq_sup`), and a zero-span piece
contributes nothing. -/
theorem windingSpan_box_eq_halves_of_collar {P : Work.CoreTopology.ParamTorus} {s : ℝ}
    {c : LeanEval.KnotTheory.PardonDistortion.R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} {Z : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (hZ : Work.PinchFamily.IsPinchCollar P s c σ u Z)
    (hspan : Work.SurgeryInvariance.WindingSpan P Z = ⊥) :
    Work.SurgeryInvariance.WindingSpan P (Work.PinchFamily.box P s c σ) =
      Work.SurgeryInvariance.WindingSpan P (Work.PinchFamily.halves P s c σ u) := by
  rw [windingSpan_box_eq_windingSpan_sdiff hZ hspan,
    windingSpan_halves_eq_windingSpan_sdiff hZ hspan]

end Work.PinchFamily
