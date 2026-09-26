import Submission.Work.SliceArcs.Defs

/-!
# The collar decomposition of the box region, and Pardon's conclusion from a span collar

This module contains the *geometric* content of the chapter, in the form in which the pinch consumes
it.  At a configuration of Pardon's box double bubble, a **collar** of the slice
(`Work.PinchFamily.IsPinchCollar`) is an open piece `Z` of the surface containing the slice trace,
contained in the region inside the box, whose complement *inside the box region* is again open.
The collar decomposition

  `boxRegion = (boxRegion ∖ Z) ∪ Z`

is then a decomposition of the box region into two **disjoint open** pieces, so every loop of the box
region lies entirely in one of them (`Work.SurgeryInvariance.Span.curve_subset_of_union`), whence the
winding span is additive over the decomposition:

  `W(boxRegion) = W(boxRegion ∖ Z) ⊔ W(Z)`.

Two consequences are proved here.

* If the collar has vanishing winding span then `W(boxRegion) ≤ W(halves)`: the collar contributes
  nothing to the winding span, and the complement of the collar inside the box lies in the two
  half-regions (`Work.PinchFamily.IsPinchCollar.sdiff_subset_halves`).
* With that, Pardon's conclusion `Work.BoxShrink.Bubble.BubbleHalf` follows *immediately*: an
  essential loop of the box region survives, with its winding vector, to one of the two
  half-regions.  Nothing else is used — no dichotomy, no general position of the box sphere, no
  sphere count.

The relevance for the arcs route is that the arc structure of the slice supplies exactly the two
properties of the slice that the plane-oriented formulations of the preceding chapter had to assume
separately: its inessentiality and its honest tameness.  What remains is the collar.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.SliceArcs

noncomputable section

variable {P : Work.CoreTopology.ParamTorus} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}

/-! ## The winding span is additive over the collar decomposition -/

/-- **The winding span of the box region is the supremum of the spans of the collar and of its
complement.**  Both pieces are open in the surface and they are disjoint, so a loop of the box region
cannot cross between them. -/
theorem box_eq_sdiff_union_of_isPinchCollar {Z : Set R3}
    (hZ : Work.PinchFamily.IsPinchCollar P s c σ u Z) :
    box P s c σ = (box P s c σ \ Z) ∪ Z := by
  ext y
  constructor
  · intro hy
    by_cases h : y ∈ Z
    · exact Set.mem_union_right _ h
    · exact Set.mem_union_left _ ⟨hy, h⟩
  · rintro (⟨hy, -⟩ | hz)
    · exact hy
    · exact hZ.subset_box hz

theorem disjoint_sdiff_of_isPinchCollar {Z : Set R3}
    (_hZ : Work.PinchFamily.IsPinchCollar P s c σ u Z) : Disjoint (box P s c σ \ Z) Z :=
  Set.disjoint_left.mpr fun _ hx hxZ => hx.2 hxZ

theorem windingSpan_box_eq_sup_of_isPinchCollar {Z : Set R3}
    (hZ : Work.PinchFamily.IsPinchCollar P s c σ u Z) :
    Work.SurgeryInvariance.WindingSpan P (box P s c σ) =
      Work.SurgeryInvariance.WindingSpan P (box P s c σ \ Z) ⊔
        Work.SurgeryInvariance.WindingSpan P Z :=
  (congrArg (fun X : Set R3 => Work.SurgeryInvariance.WindingSpan P X)
      (box_eq_sdiff_union_of_isPinchCollar hZ)).trans
    (Work.SurgeryInvariance.Span.union_eq_sup hZ.open_sdiff hZ.isOpen
      (disjoint_sdiff_of_isPinchCollar hZ))

/-- **The span containment from a collar.**  If the collar `Z` of the slice has vanishing winding
span, then the region inside the box realises no more winding vectors than the two half-regions: its
complement in the box lies in the halves, where the collar contributes nothing. -/
theorem windingSpan_box_le_halves_of_isPinchCollar {Z : Set R3}
    (hZ : Work.PinchFamily.IsPinchCollar P s c σ u Z)
    (hspan : Work.SurgeryInvariance.WindingSpan P Z = ⊥) :
    Work.SurgeryInvariance.WindingSpan P (box P s c σ) ≤
      Work.SurgeryInvariance.WindingSpan P (halves P s c σ u) := by
  have h := windingSpan_box_eq_sup_of_isPinchCollar hZ
  have hsub : box P s c σ \ Z ⊆ halves P s c σ u := by
    intro y hy
    rcases hy with ⟨hybox, hyZ⟩
    have hyslice : y ∈ slice P s c σ u → False := fun hys => hyZ (hZ.slice_subset hys)
    rcases Work.BoxShrink.Core.mem_boxRegion.mp hybox with ⟨hyc, hyb⟩
    by_contra hyh
    apply hyslice
    have hne : y.ofLp (σ 2) = c.ofLp (σ 2) + u := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact hyh (Set.mem_union_right _ (Work.BoxShrink.Core.mem_lowerRegion.mpr ⟨hyc, hyb, hlt⟩))
      · exact hyh (Set.mem_union_left _ (Work.BoxShrink.Core.mem_upperRegion.mpr ⟨hyc, hyb, hgt⟩))
    exact Work.BoxShrink.Core.mem_sliceRegion.mpr ⟨hyc, hyb, hne⟩
  have hmono : Work.SurgeryInvariance.WindingSpan P (box P s c σ \ Z) ≤
      Work.SurgeryInvariance.WindingSpan P (halves P s c σ u) :=
    Work.SurgeryInvariance.WindingSpan_mono P hsub
  rw [h, hspan, sup_bot_eq]
  exact hmono

/-! ## Pardon's conclusion from a collar of vanishing span -/

/-- **The two half-regions span the halves.**  They are disjoint and open in the surface. -/
theorem windingSpan_halves_eq_sup (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Work.SurgeryInvariance.WindingSpan P (halves P s c σ u) =
      Work.SurgeryInvariance.WindingSpan P (upper P s c σ u) ⊔
        Work.SurgeryInvariance.WindingSpan P (lower P s c σ u) :=
  Work.SurgeryInvariance.Span.union_eq_sup
    (Work.BoxShrink.Core.isOpenInCarrier_upperRegion P s c σ u)
    (Work.BoxShrink.Core.isOpenInCarrier_lowerRegion P s c σ u)
    (Work.BoxShrink.Core.disjoint_upperRegion_lowerRegion P s c σ u)

/-- **Pardon's conclusion from the span containment.**  If the winding span of the region inside the
box is contained in that of the two half-regions, then an essential loop of the box region survives
to one of the two halves. -/
theorem bubbleHalf_of_windingSpan_le_halves
    (h : Work.SurgeryInvariance.WindingSpan P (box P s c σ) ≤
      Work.SurgeryInvariance.WindingSpan P (halves P s c σ u)) :
    Work.BoxShrink.Bubble.BubbleHalf P s c σ u := by
  intro hbox
  have hne : Work.SurgeryInvariance.WindingSpan P (box P s c σ) ≠ ⊥ :=
    (Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mpr hbox
  have hneH : Work.SurgeryInvariance.WindingSpan P (halves P s c σ u) ≠ ⊥ :=
    fun hbot => hne (le_bot_iff.mp (h.trans (le_of_eq hbot)))
  rw [windingSpan_halves_eq_sup (P := P) (s := s) (c := c) (σ := σ) (u := u)] at hneH
  by_contra hcon
  have hup : ¬ P.ContainsEssentialLoop (upper P s c σ u) := fun h => hcon (Or.inl h)
  have hlo : ¬ P.ContainsEssentialLoop (lower P s c σ u) := fun h => hcon (Or.inr h)
  have hup' : Work.SurgeryInvariance.WindingSpan P (upper P s c σ u) = ⊥ :=
    (Work.SurgeryInvariance.WindingSpan_eq_bot_iff P _).mpr hup
  have hlo' : Work.SurgeryInvariance.WindingSpan P (lower P s c σ u) = ⊥ :=
    (Work.SurgeryInvariance.WindingSpan_eq_bot_iff P _).mpr hlo
  rw [hup', hlo', sup_bot_eq] at hneH
  exact hneH rfl

/-- **Pardon's conclusion at a configuration carrying a collar of vanishing winding span**: the
region inside the box, the two half-regions, and the collar of the slice — nothing else. -/
theorem bubbleHalf_of_collar {Z : Set R3} (hZ : Work.PinchFamily.IsPinchCollar P s c σ u Z)
    (hspan : Work.SurgeryInvariance.WindingSpan P Z = ⊥) :
    Work.BoxShrink.Bubble.BubbleHalf P s c σ u :=
  bubbleHalf_of_windingSpan_le_halves (windingSpan_box_le_halves_of_isPinchCollar hZ hspan)

/-- **Pardon's conclusion at a configuration whose slice carries the arc structure and whose collar
has vanishing span.**  The arc structure only enters through the *hypothesis* of the collar residual
`ArcCollarBody`; the conclusion below uses nothing but the collar. -/
theorem bubbleHalf_of_arcCondition_of_spanCollarBody (β : Work.CoreTopology.ClosedCurve P)
    (_hA : ArcCondition P s c σ u) (h : Work.PinchFamily.SpanCollarBody P β s c σ u) :
    Work.BoxShrink.Bubble.BubbleHalf P s c σ u := by
  obtain ⟨Z, hZ, hspan⟩ := h
  exact bubbleHalf_of_collar hZ hspan

/-! ## The drop form of the same conclusion

The preceding chapter's drop datum asks only for the dimension bound `finrank W(box) ≤ 1` in the case
in which the two half-regions are inessential.  The span containment of a collar gives that bound
immediately (and, when the halves are inessential, gives the stronger `W(box) = ⊥`). -/

/-- **The dimension bound of the drop case, from the span containment.** -/
theorem finrank_box_le_one_of_windingSpan_le_halves
    (h : Work.SurgeryInvariance.WindingSpan P (box P s c σ) ≤
      Work.SurgeryInvariance.WindingSpan P (halves P s c σ u))
    (hbot : Work.SurgeryInvariance.WindingSpan P (halves P s c σ u) = ⊥) :
    Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P (box P s c σ)) ≤ 1 := by
  have hbox : Work.SurgeryInvariance.WindingSpan P (box P s c σ) = ⊥ :=
    le_bot_iff.mp (h.trans (le_of_eq hbot))
  rw [hbox, finrank_bot]
  omega

/-! ## The span form and the drop form from the collar -/

/-- **The span form of the pinch from a collar of vanishing span.** -/
theorem arcSpanBody_of_spanCollarBody (β : Work.CoreTopology.ClosedCurve P)
    (h : Work.PinchFamily.SpanCollarBody P β s c σ u) :
    ArcSpanBody P β s c σ u := by
  intro _hA'
  obtain ⟨Z, hZ, hspan⟩ := h
  exact windingSpan_box_le_halves_of_isPinchCollar hZ hspan

/-- **The drop form from the span form** (with the two half-regions inessential). -/
theorem arcDropBody_of_arcSpanBody {β : Work.CoreTopology.ClosedCurve P}
    (h : ArcSpanBody P β s c σ u) : ArcDropBody P β s c σ u := by
  intro hA _hS _hZ hhalves
  exact finrank_box_le_one_of_windingSpan_le_halves (h hA) hhalves

/-- **The collar form of the pinch from the matched collar** (Pardon's description of the changed
piece gives the vanishing of its span through his Lemma 2, which the sibling chapter proves). -/
theorem arcCollarBody_of_arcNeckCollarBody {β : Work.CoreTopology.ClosedCurve P}
    (h : ArcNeckCollarBody P β s c σ u) : ArcCollarBody P β s c σ u :=
  fun hA => Work.PinchFamily.spanCollarBody_of_neckCollarBody β (h hA)

/-- **The drop form of the pinch from a collar of vanishing span.** -/
theorem arcDropBody_of_spanCollarBody (β : Work.CoreTopology.ClosedCurve P)
    (h : Work.PinchFamily.SpanCollarBody P β s c σ u) :
    ArcDropBody P β s c σ u :=
  arcDropBody_of_arcSpanBody (arcSpanBody_of_spanCollarBody β h)

end

end Work.SliceArcs
