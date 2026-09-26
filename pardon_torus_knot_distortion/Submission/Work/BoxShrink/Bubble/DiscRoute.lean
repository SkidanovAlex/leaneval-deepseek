import Submission.Work.BoxShrink.Bubble.Disc
import Submission.Work.SurgeryInvariance.WindingOf.homotopic_eq

/-!
# Pushing a loop off an embedded disc inside the box: the local model of the pinch

The last content of the chapter is the loop transport `Work.BoxShrink.Bubble.SlicePushOff`.  This file
isolates its **local form at an embedded disc**: if the slice is contained in the *interior* of an
embedded disc `D` which itself lies in the region inside the box, then it is enough to know that loops
of the region can be pushed off that disc:

  `Work.BoxShrink.Bubble.SliceDiscRoute P s c σ u D`

says that every loop of `boxRegion` is homotopic (in the surface) to a loop of
`boxRegion ∖ D.interior`.  The theorem `Work.BoxShrink.Bubble.slicePushOff_of_discRoute` then gives
the push-off for free: `boxRegion ∖ D.interior ⊆ boxRegion ∖ sliceRegion = upperRegion ∪ lowerRegion`
because `sliceRegion ⊆ D.interior`, and a homotopic loop has the same winding vector
(`Work.SurgeryInvariance.WindingOf.homotopic_eq`).

This local model is *not* the field: it only yields the push-off in the configurations in which the
slice happens to be contained in a disc inside the box (it says nothing about a slice which is spread
over the surface, e.g. several far-apart circles).  It is the statement which the pinch has to supply
near a disc-shaped piece of the slice, and it is the disc-shaped analogue of the collar/pinch
`Work.BoxShrink.Bubble.SlicePushModel`: a loop that enters `D` is rerouted along `∂D`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Bubble

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-- **The disc-routing local model**: every loop of the region inside the box is homotopic (in the
surface) to a loop avoiding the interior of the disc `D`. -/
def SliceDiscRoute (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) (D : Work.SurgeryInvariance.DiscRegion P) : Prop :=
  ∀ γ : Work.CoreTopology.ClosedCurve P,
    (∀ t : ℝ, γ t ∈ Work.BoxShrink.Core.boxRegion P s c σ) →
      ∃ γ' : Work.CoreTopology.ClosedCurve P,
        (∀ t : ℝ, γ' t ∈ Work.BoxShrink.Core.boxRegion P s c σ \ D.interior) ∧
          Work.CoreTopology.Homotopic P γ γ'

/-- **The push-off from the disc-routing local model.**  If the slice lies in the interior of an
embedded disc contained in the region inside the box, then routing the region's loops off that disc
transports them into the two half-regions: `SlicePushOff` holds. -/
theorem slicePushOff_of_discRoute {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    {D : Work.SurgeryInvariance.DiscRegion P}
    (hslice : Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ D.interior)
    (hDsub : D.carrier ⊆ Work.BoxShrink.Core.boxRegion P s c σ)
    (hroute : SliceDiscRoute P s c σ u D) : SlicePushOff P s c σ u := by
  refine (Toolkit.subset_realizedWindings_iff).mpr ?_
  intro γ hγ
  obtain ⟨γ', hγ', hhom⟩ := hroute γ hγ
  refine ⟨γ', fun t => ?_, (Work.SurgeryInvariance.WindingOf.homotopic_eq hhom).symm⟩
  have hxb : γ' t ∈ Work.BoxShrink.Core.boxRegion P s c σ := (hγ' t).1
  have hxn : γ' t ∉ D.interior := (hγ' t).2
  have hns : γ' t ∉ Work.BoxShrink.Core.sliceRegion P s c σ u := fun hs => hxn (hslice hs)
  have hsplit := Work.BoxShrink.Core.boxRegion_eq_union P s c σ u
  rw [hsplit] at hxb
  rcases hxb with h | h
  · exact h
  · exact absurd h hns

/-- **The field from the disc-routing local model** (Pardon's double bubble, in the shape of the field
`bubble` of `Work.BoxShrink.Core.BubbleInput`, whenever the slice lies in a disc inside the box). -/
noncomputable def bubbleSweep_of_discRoute {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    {D : Work.SurgeryInvariance.DiscRegion P}
    (hslice : Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ D.interior)
    (hDsub : D.carrier ⊆ Work.BoxShrink.Core.boxRegion P s c σ)
    (hroute : SliceDiscRoute P s c σ u D) :
    Work.BoxShrink.Core.BubbleSweep P s c σ u :=
  bubble_of_slicePushOff (slicePushOff_of_discRoute (P := P) hslice hDsub hroute)

/-! ## The interface that consumes `hS`

The field's hypothesis `¬ P.ContainsEssentialLoop (sphereSet c σ s)` (Pardon's sphere count) is *not*
used by the push-off, and the push-off is *false* in some configurations in which `hS` fails (an annulus
in the surface cut by an arc has an essential core loop whose class is lost on either side, and its
boundary curves are then essential — see `PLAN.md`, stretch 13).  The general form of the last mile is
therefore the push-off **under the field's own hypotheses**, and this is the interface through which a
future proof should consume `hS`: -/

/-- **The remaining input, with the field's hypotheses exposed**: the push-off for every box/plane
configuration whose *two* cuts carry no essential loop.  A proof of this statement is a proof of the
field (`Work.BoxShrink.Bubble.bubble_of_collarAll`); the difference from
`Work.BoxShrink.Bubble.PushOffInput` is that here `hS` is available, and it is exactly what the routing
of a path around the components of the slice has to consume. -/
def CollarInput : Prop :=
  ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s) →
    ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u) →
    SlicePushOff P s c σ u

/-- **The field from the push-off under the field's own hypotheses.**

`Work.BoxShrink.Bubble.CollarInput` is the push-off restricted to the configurations to which the field
itself applies (both cuts inessential).  A proof of it discharges the push-off hypothesis of
`Work.BoxShrink.Bubble.bubble_of_pushOffAll` and hence gives the field in the exact shape of
`Work.BoxShrink.Core.BubbleInput.bubble`.  It is the interface in which the sphere hypothesis `hS` is
available — that is, in which the routing argument for the pinch has something to consume. -/
noncomputable def bubble_of_collarAll (h : CollarInput) :
    ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s) →
      ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u) →
      Work.BoxShrink.Core.BubbleSweep P s c σ u := by
  intro P s c σ u hS hZ
  have h' : ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
      (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s) →
      ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u) →
      SlicePushOff P s c σ u := h
  exact bubble_of_slicePushOff (h' P s c σ u hS hZ)

end

end Work.BoxShrink.Bubble
