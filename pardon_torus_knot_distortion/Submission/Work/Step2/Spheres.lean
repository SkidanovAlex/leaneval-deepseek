import Submission.Work.Step2.Bubble
import Submission.Work.Step2.halfAbove_isEmbeddedSphere
import Submission.Work.Step2.halfBelow_isEmbeddedSphere
import Submission.Work.Topology.SphereSlicing.All

/-!
# Pardon's double bubble for the box: the three spheres

Pardon's double bubble for the box is the pair `(S, D)` with `S = ∂PBox s c σ` and
`D = cutDisc s c σ u` the flat disc cut out of the box by the plane, glued to `S` along the gluing
circle `boundaryCircle = ∂D = S ∩ {plane}`.  Its two halves are the spheres `H₁ = halfAbove` and
`H₂ = halfBelow`, whose interiors are the two half-boxes (`Bubble.closure_upperBody_eq` and
`Geometry.upperRegion_eq_carrier_upperBody`), so that the traced regions of the two halves are the
crux's `upperRegion` and `lowerRegion`.

This module records that the three surfaces are *embedded spheres* — the hypothesis under which
Pardon's innermost-disc input (`Work.InnermostDisk.IsEmbeddedSphere`) and his Lemma 2 apply:

* `sphereSet_isEmbeddedSphere` — the box sphere (from `Work.Topology.SphereSlicing.isEmbeddedSphere_BoxSphere`);
* `halfAbove_isEmbeddedSphere`, `halfBelow_isEmbeddedSphere` — the two halves of the double bubble,
  i.e. the two spheres at which the pinching family of Pardon's Step 2 arrives.

The hypotheses `0 < s` and `|u| < boxSide 2 * s` say that the box is nondegenerate and that the plane
meets its interior — exactly the condition under which the cut produces a genuine double bubble.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Step2

noncomputable section

/-- **The box sphere is an embedded sphere.** -/
theorem sphereSet_isEmbeddedSphere {s : ℝ} (hs : 0 < s) (c : R3) (σ : Equiv.Perm (Fin 3)) :
    Work.InnermostDisk.IsEmbeddedSphere (Work.BoxShrink.Core.sphereSet c σ s) :=
  Work.Topology.SphereSlicing.isEmbeddedSphere_BoxSphere hs c σ

/-- **The first half of Pardon's double bubble is an embedded sphere** — the boundary of the upper
half-box. -/
theorem halfAbove_isEmbeddedSphere' {s : ℝ} (hs : 0 < s) (c : R3) (σ : Equiv.Perm (Fin 3)) {u : ℝ}
    (hu : |u| < Submission.boxSide 2 * s) :
    Work.InnermostDisk.IsEmbeddedSphere (halfAbove s c σ u) :=
  halfAbove_isEmbeddedSphere hs c σ hu

/-- **The second half of Pardon's double bubble is an embedded sphere.** -/
theorem halfBelow_isEmbeddedSphere' {s : ℝ} (hs : 0 < s) (c : R3) (σ : Equiv.Perm (Fin 3)) {u : ℝ}
    (hu : |u| < Submission.boxSide 2 * s) :
    Work.InnermostDisk.IsEmbeddedSphere (halfBelow s c σ u) :=
  halfBelow_isEmbeddedSphere hs c σ hu

/-- **The two halves of the double bubble are embedded spheres, and they cover the footprint of the
pinching family.**  This is the endpoint datum of Pardon's Step 2: the family `{S_t}` starts at the
box sphere and ends at the two spheres `H₁, H₂`. -/
theorem doubleBubble_halves {s : ℝ} (hs : 0 < s) (c : R3) (σ : Equiv.Perm (Fin 3)) {u : ℝ}
    (hu : |u| < Submission.boxSide 2 * s) :
    Work.InnermostDisk.IsEmbeddedSphere (halfAbove s c σ u) ∧
      Work.InnermostDisk.IsEmbeddedSphere (halfBelow s c σ u) ∧
      halfAbove s c σ u ∪ halfBelow s c σ u = footprint s c σ u :=
  ⟨halfAbove_isEmbeddedSphere hs c σ hu, halfBelow_isEmbeddedSphere hs c σ hu,
    (footprint_eq_union s c σ u).symm⟩

end

end Work.Step2
