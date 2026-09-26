import Submission.Work.BoxShrink.Core.Defs
import Submission.Work.BoxShrink.Core.Basic
import Submission.Work.SurgeryInvariance.API
import Submission.Work.PinchCounted.Assemble

/-!
# `Work.Step2` — Pardon's Step 2: the explicit double bubble of the box

This is the vocabulary module of the chapter.  It fixes the *explicit* geometry of Pardon's double
bubble for the self-similar box `Submission.PBox s c σ` cut by the plane
`{y (σ 2) = c (σ 2) + u}`:

* `upperCap`, `lowerCap` — the two halves of the box sphere `∂PBox s c σ = sphereSet c σ s` cut by
  the plane; `boundaryCircle` — the circle `∂D` along which the flat disc is glued to the sphere;
* `halfAbove = upperCap ∪ cutDisc` and `halfBelow = lowerCap ∪ cutDisc` — Pardon's two halves
  `H₁, H₂` of the double bubble (each is a sphere: the boundary of one of the two half-boxes);
* `footprint = sphereSet ∪ cutDisc` — Pardon's `S ∪ D`, the set over which the `2`-surgery family
  lives (his "by construction" bound on `#(S_t ∩ β)` is a statement about this set);
* `upperBody = PBox ∩ upperHalf`, `lowerBody = PBox ∩ lowerHalf` — the two half-*boxes*, i.e. the
  solid bodies whose boundaries are `halfAbove`, `halfBelow`;
* `pinchSolid t`, `pinchRegion t` — the explicit one-parameter family of *solid* regions along which
  the box is pinched: at `t = 0` the box itself, at `t = 1` the box minus the cutting disc, so that
  the traced region of the surface runs from `boxRegion` to the two half-regions;
* `slab (w)`, `band (w w')` — the flat slab and the flat band around the cutting plane, through
  which the pinch passes.

The mathematical results are in the sibling modules: `Geometry.lean` (the point-set geometry),
`Count.lean` (Pardon's count), `Pinch.lean` (the family and the residual), `Assemble.lean` (the
reduction to `CountingHalf` and the challenge).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Step2

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-! ## The pieces of Pardon's double bubble -/

/-- **The upper cap**: the part of the box sphere `∂PBox s c σ` strictly above the cutting plane
`{y (σ 2) = c (σ 2) + u}`.  It is one of the two discs into which the plane cuts the sphere. -/
def upperCap (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) : Set R3 :=
  Work.BoxShrink.Core.sphereSet c σ s ∩ Work.BoxShrink.Core.upperHalf c σ u

/-- **The lower cap**: the part of the box sphere strictly below the cutting plane. -/
def lowerCap (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) : Set R3 :=
  Work.BoxShrink.Core.sphereSet c σ s ∩ Work.BoxShrink.Core.lowerHalf c σ u

/-- **The gluing circle** `∂D` of the double bubble: the trace of the cutting plane on the box sphere.
It is the common boundary of the two caps, and the boundary of the flat disc `cutDisc s c σ u`. -/
def boundaryCircle (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) : Set R3 :=
  Work.BoxShrink.Core.sphereSet c σ s ∩ Work.BoxShrink.Core.cutPlane c σ u

/-- **The part of the box sphere weakly above the cutting plane**: the closed upper cap, i.e. the
upper cap together with the gluing circle. -/
def closedUpperCap (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) : Set R3 :=
  Work.BoxShrink.Core.sphereSet c σ s ∩ {y : R3 | c (σ 2) + u ≤ y (σ 2)}

/-- **The part of the box sphere weakly below the cutting plane**. -/
def closedLowerCap (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) : Set R3 :=
  Work.BoxShrink.Core.sphereSet c σ s ∩ {y : R3 | y (σ 2) ≤ c (σ 2) + u}

/-- **Pardon's first half** `H₁` of the double bubble: the closed upper cap glued to the flat disc
along the gluing circle.  As a set it is `upperCap ∪ boundaryCircle ∪ cutDisc`; it is a sphere,
namely the boundary of the upper half-box `upperBody` (`halfAbove_eq_frontier_upperBody`). -/
def halfAbove (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) : Set R3 :=
  closedUpperCap s c σ u ∪ Work.BoxShrink.Core.cutDisc s c σ u

/-- **Pardon's second half** `H₂` of the double bubble. -/
def halfBelow (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) : Set R3 :=
  closedLowerCap s c σ u ∪ Work.BoxShrink.Core.cutDisc s c σ u

/-- **The footprint of the pinching family**: Pardon's `S ∪ D`.  The whole `2`-surgery family of
spheres lives over this set — this is the "by construction" locality which produces his count
`#(S_t ∩ β) ≤ #(S ∩ β) + 2 #(D ∩ β)` (see `Count.lean`). -/
def footprint (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) : Set R3 :=
  Work.BoxShrink.Core.sphereSet c σ s ∪ Work.BoxShrink.Core.cutDisc s c σ u

/-- **The upper half-box**: the solid body of which `halfAbove` is the boundary. -/
def upperBody (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) : Set R3 :=
  Submission.PBox s c σ ∩ Work.BoxShrink.Core.upperHalf c σ u

/-- **The lower half-box**: the solid body of which `halfBelow` is the boundary. -/
def lowerBody (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) : Set R3 :=
  Submission.PBox s c σ ∩ Work.BoxShrink.Core.lowerHalf c σ u

/-- **The flat slab** of half-width `w` around the cutting plane. -/
def slab (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) (w : ℝ) : Set R3 :=
  {y : R3 | |y (σ 2) - (c (σ 2) + u)| < w}

/-- **The open flat band** between the two slab half-widths `w < w'`. -/
def band (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) (w w' : ℝ) : Set R3 :=
  {y : R3 | w < |y (σ 2) - (c (σ 2) + u)| ∧ |y (σ 2) - (c (σ 2) + u)| < w'}

/-- **The closed flat band** between the two slab half-widths `w < w'`: the shape of the neck piece
of the pinching family. -/
def closedBand (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) (w w' : ℝ) : Set R3 :=
  {y : R3 | w < |y (σ 2) - (c (σ 2) + u)| ∧ |y (σ 2) - (c (σ 2) + u)| ≤ w'}

/-! ## The explicit pinching family of solid regions -/

/-- **The `t`-th solid region of the pinching of the box.**  The box with the closed slab of
half-width `t - 1` around the cutting plane removed; for `t ≤ 1` this is the box minus a slab, for
`t = 1` the box minus the cutting disc itself.

The parameter is chosen so that the family starts *before* the pinch (`t = 0`, where the slab has
half-width `-1` and nothing is removed: the whole box) and ends exactly at the two half-boxes
(`t = 1`). -/
def pinchSolid (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) (t : ℝ) : Set R3 :=
  Submission.PBox s c σ ∩ {y : R3 | t - 1 < |y (σ 2) - (c (σ 2) + u)|}

/-- **The region of the surface inside the `t`-th pinching sphere**: `F ∩ int(S_t)`.  At `t = 0`
this is the region inside Pardon's box, and at `t = 1` it is the two half-regions.  This is the
*explicit* candidate for the region family of Pardon's Step 2. -/
def pinchRegion (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) (t : ℝ) : Set R3 :=
  P.carrier ∩ pinchSolid s c σ u t

/-- **The changed piece of the pinch between the parameters `t` and `r`**: the part of the surface
which the `2`-surgery adds to (or removes from) the region of the pinch when the slab grows from
half-width `t - 1` to half-width `r - 1`.  It is the trace on the surface of the solid band between
the two slabs — Pardon's "pinched neck". -/
def neckPiece (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) (t r : ℝ) : Set R3 :=
  P.carrier ∩ (pinchSolid s c σ u t \ pinchSolid s c σ u r)

end

end Work.Step2
