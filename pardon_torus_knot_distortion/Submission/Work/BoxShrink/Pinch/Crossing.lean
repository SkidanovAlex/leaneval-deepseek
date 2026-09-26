import Submission.Work.BoxShrink.Pinch.Bridge
import Submission.Work.BoxShrink.Pinch.SlicingLoops
import Submission.Work.BoxShrink.Pinch.PlanePathDefs

/-!
# What the residual really is: the crossing analysis of the slice

`SweepChain.lean` reduces the pinch to Pardon's per-step assertion along a sweep.  This module
records the *other* road to the same place, which was followed in this stretch of work to the point
at which the remaining content is a statement about **intersection numbers**, and which is the state
of the art for the next stretch.  The point of writing it down is that the residual is *not* a
homological statement about the box region and the halves: it is the conjunction of two statements
about the *cutting plane* that a surface theorist can attack with the classical tools (the
intersection form on the torus, and the cancellation of opposite-sign crossings), and the module
proves the elementary half of the first one.

## The crossing analysis

Let `F` be the torus of the challenge, `P` the cutting plane and `Ω = F ∩ Box` the box region.  The
slice `Z = F ∩ Ω ∩ P` is the trace of `P` inside the box, a finite union of arcs and circles
(`TameSlice`), and each of its components lies in a component of the *full* trace `F ∩ P`, which is
a disjoint union of circles (`TransverseSlice`).  Two facts about these circles are the crux:

**(K0) the trace's classes are collinear.**  Two components of `F ∩ P` are disjoint simple closed
curves of `F`; for two disjoint 1-cycles of a surface the *algebraic* intersection number vanishes,
and the intersection form on `H₁(T²) = ℚ²` is non-degenerate, so two *independent* classes could not
be realised by disjoint curves.  Hence there is a line `L ⊆ H₁(T²;ℚ)` containing the class of every
component of `F ∩ P` — in particular of every *closing circle* `w` of a slice arc (the arc lies in
`F ∩ Ω`, and `w \ arc` lies outside the box, which is how the endpoints of a slice arc are joined
outside `Ω`).

**(K2) zero crossing numbers are avoidable.**  For a closed curve `z ⊆ F` and a loop `γ ⊆ Ω`, the
algebraic intersection number of `γ` with `z` is computed by the winding vectors alone,
`γ · z = [γ] · [z] ∈ ℚ`, and if it vanishes then `γ` can be homotoped *inside* `Ω` to a loop
disjoint from `z`.  (For a slice *arc* `a`, the same statement holds with the closing circle `w_a`:
`γ · a = [γ] · [w_a]`, since `γ` misses the part of `w_a` outside the box.  This is the identity
that makes the analysis work, and it is why `hZ` — the vanishing of the winding span of the slice —
is not enough on its own: the closing circles are *not* slice components.)

Granting (K0) and (K2), the pinch follows: if `u ∈ W(Ω)` and `u ⊥ L`, then every representative
loop of `u` has zero crossing number with every slice component, hence can be homotoped off the
slice, so `u ∈ W(Ω \ Z)`; hence

  `W(Ω) ∩ L^⊥ ⊆ W(Ω \ Z)`,   and since `dim L ≤ 1`,   `dim W(Ω) ≤ dim W(Ω \ Z) + 1`,

which is `Work.BoxShrink.Pinch.PinchNoJump` (and, with the dichotomy, `BubbleHalf`).  The `+1` is
needed: at the standard small box (`Work.BoxShrink.Pinch.BubbleHalfRefuted`) the trace is
*essential*, so `L ≠ 0`, and the drop really is one.

## What is proved here

* `Work.BoxShrink.Pinch.not_periodRealised_sliceRegion_of_hZ` — `hZ` read in the parameter plane:
  no nonzero lattice period is realised by a path of the slice's preimage.  This is the hypothesis
  that (K2) has to be applied to, and it is exactly `¬ P.ContainsEssentialLoop sliceRegion` by the
  dictionary `Work.BoxShrink.Pinch.containsEssentialLoop_of_periodicPath`.
* `Work.BoxShrink.Pinch.planePreimage_sliceRegion` — the slice's preimage is the intersection of the
  box's preimage with the cut plane's preimage, the form in which (K2) has to be stated (the closing
  path of an arc is a path of the *plane's* preimage which lies outside the box's preimage).
* `Work.BoxShrink.Pinch.sliceRegion_subset_cutDisc` — the slice lies in the cut disc, so its arcs end
  on the disc's boundary circle `F ∩ ∂D ⊆ F ∩ ∂Box` (an inessential component of the box trace, by
  `hS`).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Pinch

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-! ## `hZ` in the parameter plane -/

/-- **`hZ` read in the plane: the slice realises no nonzero lattice period.**  If the region of the
slice carries no essential loop, then no nonzero period of the lattice is realised by a path of its
preimage.  (This is the contrapositive of `containsEssentialLoop_of_periodicPath`, the plane half of
the dictionary; the other half is used in the direction "a realised period gives an essential
loop".) -/
theorem not_periodRealised_sliceRegion_of_hZ {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hZ : ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u)) {k l : ℤ}
    (h : PeriodRealised P (Work.BoxShrink.Core.sliceRegion P s c σ u) k l) : (k, l) = 0 := by
  by_contra hne
  obtain ⟨q, hq, hper, hmem⟩ := h
  refine hZ (containsEssentialLoop_of_periodicPath (P := P) hq ?_ hne hmem)
  intro t
  have := hper t
  simpa only [Work.TorusCover.periodShift] using this

/-- **The slice's preimage is the trace of the cut disc.**  In the parameter plane the slice is the
intersection of the preimage of the box with the preimage of the cutting plane; the closing path of
a slice arc is a path of the second factor which avoids the first. -/
theorem planePreimage_sliceRegion (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    planePreimage P (Work.BoxShrink.Core.sliceRegion P s c σ u) =
      planePreimage P (Submission.PBox s c σ) ∩
        planePreimage P (Work.BoxShrink.Core.cutPlane c σ u) := by
  ext q
  simp only [mem_planePreimage, Work.BoxShrink.Core.mem_sliceRegion, Set.mem_inter_iff]
  tauto

/-- **The slice lies in the cut disc**, hence its arcs end on the circle
`F ∩ ∂D ⊆ F ∩ ∂Box`, a component of the trace of the box sphere. -/
theorem sliceRegion_subset_cutDisc (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Work.BoxShrink.Core.sliceRegion P s c σ u ⊆
      P.carrier ∩ Work.BoxShrink.Core.cutDisc s c σ u := by
  rw [sliceRegion_eq_carrier_inter_cutDisc]

/-- **The slice is the part of the box region cut by the plane.**  The two halves and the slice
partition the box region, so a loop of the box region either lies in one of the halves or meets the
slice — the dichotomy of the loop-level analysis of `Work.BoxShrink.Pinch.HalfSplit`. -/
theorem boxRegion_eq_halves_union_slice (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Work.BoxShrink.Core.boxRegion P s c σ =
      (Work.BoxShrink.Core.upperRegion P s c σ u ∪
        Work.BoxShrink.Core.lowerRegion P s c σ u) ∪
      Work.BoxShrink.Core.sliceRegion P s c σ u :=
  Work.BoxShrink.Core.boxRegion_eq_union P s c σ u

end

end Work.BoxShrink.Pinch
