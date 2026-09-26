import Submission.Work.BoxShrink.Bubble.Reduce
import Submission.Work.BoxShrink.Bubble.Transport.slicePushOff_of_deformation

/-!
# The local model of the pinch: a one-sided push of a neighbourhood of the slice

The geometric input of the chapter, `Work.BoxShrink.Bubble.SlicePushOff`, says that the loops of
the region inside the box can be transported off the slicing plane.  This file reduces that input
to the *local* datum which is Pardon's pinch:

`Work.BoxShrink.Bubble.SlicePushModel P s c σ u`: an open (in the surface) neighbourhood `N` of the
slice together with a one-parameter deformation `H` of `ℝ³` which

* is supported in `N` (`H r x = x` for `x ∉ N`), preserves the surface, and starts at the identity;
* carries `N` into `upperRegion ∪ lowerRegion` at time `1`.

Nothing is required of the points outside `N`: a loop of `boxRegion` which does not meet `N` does
not meet the slice either (because `sliceRegion ⊆ N`) and therefore already lies in
`boxRegion ∖ sliceRegion = upperRegion ∪ lowerRegion`.

`Work.BoxShrink.Bubble.slicePushOff_of_pushModel` proves that such a model gives the input, so a
sibling subproject can discharge the topological content of Pardon's pinch by producing the model
(the collar structure of the slice in the surface: near a point of the slice the surface is locally
a disc cut by an arc, whose two sides are the two half-regions, and the ends of the arcs lie on
`∂PBox`).  The model is *local*: it is a statement about a neighbourhood of the slice only.

The degenerate instance in which the plane misses the region is `slicePushModel_of_empty_slice`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Bubble

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-- **The local model of Pardon's pinch**: an open neighbourhood `N` of the slice, together with a
deformation of `ℝ³` supported in `N`, preserving the surface and carrying `N` into the union of the
two half-regions. -/
structure SlicePushModel (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) where
  /-- the neighbourhood of the slice in which the pinch takes place -/
  N : Set R3
  /-- it contains the slice -/
  slice_subset : Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ N
  /-- the deformation -/
  H : ℝ → R3 → R3
  /-- it is continuous in the parameter and the point -/
  cont : Continuous (Function.uncurry H)
  /-- it starts at the identity -/
  zero : ∀ x : R3, H 0 x = x
  /-- it preserves the surface -/
  mem : ∀ (r : ℝ) (x : R3), x ∈ P.carrier → H r x ∈ P.carrier
  /-- it is supported in `N` -/
  fixed_outside : ∀ (r : ℝ) (x : R3), x ∉ N → H r x = x
  /-- at time `1` the neighbourhood has been pushed into the two half-regions -/
  maps : ∀ x ∈ N, H 1 x ∈ Work.BoxShrink.Core.upperRegion P s c σ u ∪
    Work.BoxShrink.Core.lowerRegion P s c σ u

/-- **The local model gives the input.** -/
theorem slicePushOff_of_pushModel {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (M : SlicePushModel P s c σ u) : SlicePushOff P s c σ u := by
  refine Transport.slicePushOff_of_deformation M.H M.cont M.zero M.mem (fun x hx => ?_)
  by_cases hN : x ∈ M.N
  · exact M.maps x hN
  · rw [M.fixed_outside 1 x hN]
    have hbox : x ∈ Work.BoxShrink.Core.upperRegion P s c σ u ∪
        Work.BoxShrink.Core.lowerRegion P s c σ u ∪
        Work.BoxShrink.Core.sliceRegion P s c σ u := by
      rw [← Work.BoxShrink.Core.boxRegion_eq_union]
      exact hx
    rcases hbox with h | h
    · exact h
    · exact absurd (M.slice_subset h) hN

/-- **Non-vacuity: the model holds when the plane misses the region.** -/
theorem slicePushModel_of_empty_slice {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : Work.BoxShrink.Core.sliceRegion P s c σ u = ∅) :
    Nonempty (SlicePushModel P s c σ u) := by
  refine ⟨{ N := ∅
            slice_subset := h.le
            H := fun _ x => x
            cont := continuous_snd
            zero := fun _ => rfl
            mem := fun _ _ hx => hx
            fixed_outside := fun _ _ _ => rfl
            maps := by simp }⟩

end

end Work.BoxShrink.Bubble
