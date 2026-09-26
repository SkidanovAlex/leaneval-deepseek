import Submission.Work.BoxShrink.PinchOff.Tamed
import Submission.Work.BoxShrink.PinchOff.Dichotomy

/-!
# The tamed residual is exactly the tamed dimension bound

`Tamed.lean` names the corrected residual `SmoothHalfSTame` (= the parent chapter's
`PushOffHalfTame`, Pardon's Lemma 3 with a transverse and tame slice) and its dimension-bound form
`KeyTame` (the tamed analogue of `Key`), and proves one direction: Pardon's conclusion at a
configuration gives the `+1` bound there (`keyTame_of_smoothHalfSTame`).

This module proves the **converse** — the tamed dimension bound gives Pardon's conclusion — using
the dichotomy at the box region, which is now available unconditionally:
`pardonDichotomy_boxRegion` (`Dichotomy.lean`, from the discharged Pardon equation (1)) says that
under `hS` the winding span of the box region is `⊥` or `⊤`.

Hence, under the box-sphere general position `BoxSliceNice`,

  `KeyTame  ↔  SmoothHalfSTame`   (`keyTame_iff_smoothHalfSTame`)

so the two forms of the tamed residual — the dimension bound of the parent chapter's §18 and the
conclusion of Pardon's Lemma 3 — are the *same statement*.  In particular a future proof only has
to produce the bound
`finrank W(Ω) ≤ finrank W(Ω⁺ ∪ Ω⁻) + 1` for a transverse tame configuration.

The proof of `pushOffHalfTame_of_keyTame` is three lines of linear algebra: if the box region is
inessential its span is `⊥` and the bound is trivial; otherwise the dichotomy makes its span `⊤`
(dimension `2`), the bound then forces the halves' span to have dimension `≥ 1`, and the halves'
span is the supremum of the two halves' spans (they are disjoint open pieces of the surface), so one
of them carries an essential loop.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

/-- **The tamed dimension bound gives Pardon's Lemma 3 conclusion**, given the general position of
the box-sphere trace (`BoxSliceNice`). -/
theorem pushOffHalfTame_of_keyTame (hnice : Work.BoxShrink.Pinch.BoxSliceNice)
    (h : KeyTame) : Work.BoxShrink.Pinch.PushOffHalfTame := by
  intro ψ s c σ u hT hTame hS hZ hbox
  -- the box region's span is `⊥` or `⊤` (Pardon's equation (2.1) at the box sphere)
  have hdich := pardonDichotomy_boxRegion (ψ := ψ) (s := s) (c := c) (σ := σ)
    (hnice ψ s c σ) hS
  have htop : Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ) = ⊤ := by
    rcases hdich with hbot | htop
    · exact absurd hbox ((Work.SurgeryInvariance.WindingSpan_eq_bot_iff _ _).mp hbot)
    · exact htop
  have hfin2 : Module.finrank ℚ
      ↥(Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ)) = 2 := by
    rw [htop, finrank_top, Module.finrank_prod]
    simp
  -- the tamed bound
  have hbound := h ψ s c σ u hT hTame hS hZ
  rw [hfin2] at hbound
  -- hence the halves' span has dimension at least one
  have hne : Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u) ≠ ⊥ := by
    intro hH
    rw [hH, finrank_bot] at hbound
    omega
  -- the halves' span is the supremum of the two halves' spans
  rw [Work.SurgeryInvariance.Span.union_eq_sup (P := surface ψ)
      (Work.BoxShrink.Core.isOpenInCarrier_upperRegion (surface ψ) s c σ u)
      (Work.BoxShrink.Core.isOpenInCarrier_lowerRegion (surface ψ) s c σ u)
      (Work.BoxShrink.Core.disjoint_upperRegion_lowerRegion (surface ψ) s c σ u)] at hne
  rcases not_and_or.mp (fun hh : Work.SurgeryInvariance.WindingSpan (surface ψ)
        (HalfUp ψ s c σ u) = ⊥ ∧ Work.SurgeryInvariance.WindingSpan (surface ψ)
          (HalfDown ψ s c σ u) = ⊥ => hne (by rw [hh.1, hh.2, sup_bot_eq])) with hup | hlo
  · exact Or.inl ((Work.SurgeryInvariance.windingSpan_ne_bot_iff _ _).mp hup)
  · exact Or.inr ((Work.SurgeryInvariance.windingSpan_ne_bot_iff _ _).mp hlo)

/-- The same, in the form of the corrected residual of this chapter. -/
theorem smoothHalfSTame_of_keyTame (hnice : Work.BoxShrink.Pinch.BoxSliceNice) (h : KeyTame) :
    SmoothHalfSTame :=
  pushOffHalfTame_of_keyTame hnice h

/-- **The two forms of the tamed residual are the same statement** (given the general position of
the box-sphere trace). -/
theorem keyTame_iff_smoothHalfSTame (hnice : Work.BoxShrink.Pinch.BoxSliceNice) :
    KeyTame ↔ SmoothHalfSTame :=
  ⟨fun h => smoothHalfSTame_of_keyTame hnice h, fun h => keyTame_of_smoothHalfSTame h⟩

end

end Work.BoxShrink.PinchOff
