import Submission.Work.BoxShrink.PinchOff.KeyTame
import Submission.Work.BoxShrink.PinchOff.OpenArcs
import Submission.Work.BoxShrink.PinchOff.tameClosedSlice_of_tameSlice

/-!
# The residual of the pinch, with the box-sphere hypothesis

`RefuteNC/Main.lean` refutes the chapter's uncounted residual family — `TracePerpSliceBox`,
`TraceClosedSliceResidual`, `TraceClosedNonCompactSlice`, and the parent chapter's
`TracePerpRealisableAll` — at the explicit configuration of `RefuteNC/Config.lean`.  The
hypothesis which that configuration violates is **`hS`**, the inessentiality of the trace of the
*box sphere* `∂PBox s c σ`: there the level set `{y = 9/10}` meets the surface in two essential
circles, and it is precisely Pardon's counting argument (his Lemma 2, `mustbeinessential`) which
supplies `hS` at every intermediate sphere of his pinching family.

This module records the corrected residual, in the honest tameness `TameClosedSlice` (the arcs of a
genuine trace are open at their ends, so `TameSlice` is too strong) and with `hS` carried:

* `KeyTameClosed` — the dimension bound `finrank W(Ω) ≤ finrank W(Ω⁺ ∪ Ω⁻) + 1` at a transverse,
  closed-tame configuration whose box-sphere trace and slice both carry no essential loop;
* `bubbleHalf_of_keyTameClosed` — the **converse direction**, which makes the bound Pardon's Lemma 3
  conclusion (`BubbleHalf`) under the box-sphere general position `BoxSliceNice`, by the
  unconditional dichotomy at the box region (`pardonDichotomy_boxRegion`, Pardon's equation (1)).

So the honest open obligation of the area is exactly: *prove `KeyTameClosed`* (equivalently, prove
Pardon's Lemma 3 conclusion at those configurations).  `KeyTameClosed` implies the chapter's
`KeyTame` by the dictionary `tameClosedSlice_of_tameSlice` (`keyTame_of_keyTameClosed` below), and
its conclusion is *not* refuted by any known configuration: the two known refutations of the
uncounted statement fail exactly one hypothesis each (the tangent configuration of
`KeyRefuted.lean` violates transversality, the configuration of `RefuteNC` violates `hS`).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

/-- **The honest residual of the pinch**: the dimension bound of a single `2`-surgery, at a
transverse and *closed-tame* configuration whose box sphere (`hS`) and slice (`hZ`) carry no
essential loop. -/
def KeyTameClosed : Prop :=
  ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u → TameClosedSlice ψ s c σ u →
    ¬ (surface ψ).ContainsEssentialLoop (SphereTrace s c σ) →
    ¬ (surface ψ).ContainsEssentialLoop (Sigma ψ s c σ u) →
    Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ)) ≤
      Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u)) + 1

/-- The honest residual implies the tamed one (the tameness hypothesis of `KeyTame` is stronger). -/
theorem keyTame_of_keyTameClosed (h : KeyTameClosed) : KeyTame :=
  fun ψ s c σ u hT hTa hS hZ =>
    h ψ s c σ u hT (tameClosedSlice_of_tameSlice ψ s c σ u hTa) hS hZ

/-- **The honest residual gives Pardon's Lemma 3 conclusion**, under the general position of the
box-sphere trace.  This is Pardon's dichotomy at the box region (`pardonDichotomy_boxRegion`): under
`hS` the winding span of the box region is `⊥` or `⊤`, so the bound `finrank W(Ω) ≤
finrank W(Ω⁺ ∪ Ω⁻) + 1` forces one of the two half-regions to carry an essential loop as soon as
`Ω` does. -/
theorem bubbleHalf_of_keyTameClosed (hnice : Work.BoxShrink.Pinch.BoxSliceNice)
    (h : KeyTameClosed) :
    ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u → TameClosedSlice ψ s c σ u →
      ¬ (surface ψ).ContainsEssentialLoop (SphereTrace s c σ) →
      ¬ (surface ψ).ContainsEssentialLoop (Sigma ψ s c σ u) →
      Work.BoxShrink.Bubble.BubbleHalf (surface ψ) s c σ u := by
  intro ψ s c σ u hT hTa hS hZ hbox
  have hdich := pardonDichotomy_boxRegion (ψ := ψ) (s := s) (c := c) (σ := σ) (hnice ψ s c σ) hS
  have htop : Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ) = ⊤ := by
    rcases hdich with hbot | htop
    · exact absurd hbox ((Work.SurgeryInvariance.WindingSpan_eq_bot_iff _ _).mp hbot)
    · exact htop
  have hfin2 : Module.finrank ℚ
      ↥(Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ)) = 2 := by
    rw [htop, finrank_top, Module.finrank_prod]
    simp
  have hbound := h ψ s c σ u hT hTa hS hZ
  rw [hfin2] at hbound
  have hne : Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u) ≠ ⊥ := by
    intro hH
    rw [hH, finrank_bot] at hbound
    omega
  rw [Work.SurgeryInvariance.Span.union_eq_sup (P := surface ψ)
      (Work.BoxShrink.Core.isOpenInCarrier_upperRegion (surface ψ) s c σ u)
      (Work.BoxShrink.Core.isOpenInCarrier_lowerRegion (surface ψ) s c σ u)
      (Work.BoxShrink.Core.disjoint_upperRegion_lowerRegion (surface ψ) s c σ u)] at hne
  rcases not_and_or.mp (fun hh : Work.SurgeryInvariance.WindingSpan (surface ψ)
        (HalfUp ψ s c σ u) = ⊥ ∧ Work.SurgeryInvariance.WindingSpan (surface ψ)
          (HalfDown ψ s c σ u) = ⊥ => hne (by rw [hh.1, hh.2, sup_bot_eq])) with hup | hlo
  · exact Or.inl ((Work.SurgeryInvariance.windingSpan_ne_bot_iff _ _).mp hup)
  · exact Or.inr ((Work.SurgeryInvariance.windingSpan_ne_bot_iff _ _).mp hlo)

/-- **The converse**: Pardon's Lemma 3 conclusion at those configurations gives the honest dimension
bound.  So the two honest forms of the residual — the dimension bound `KeyTameClosed` and the
conclusion `BubbleHalf` with `hS` and `TameClosedSlice` — are the *same* statement, and a future
proof may attack either. -/
theorem keyTameClosed_of_bubbleHalf
    (h : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u → TameClosedSlice ψ s c σ u →
      ¬ (surface ψ).ContainsEssentialLoop (SphereTrace s c σ) →
      ¬ (surface ψ).ContainsEssentialLoop (Sigma ψ s c σ u) →
      Work.BoxShrink.Bubble.BubbleHalf (surface ψ) s c σ u) :
    KeyTameClosed :=
  fun ψ s c σ u hT hTa hS hZ =>
    keyTame_of_bubbleHalf (h ψ s c σ u hT hTa hS hZ)

end

end Work.BoxShrink.PinchOff
