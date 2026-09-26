import Mathlib
import Submission.Work.Drive.Mono.TiltedTraceData
import Submission.Work.Sweep.AeTransverseCoord.ae_transverse_coord

/-!
# The transversality of the cutting plane

Pardon's pinching family is counted at the *cutting plane* `{y (σ 2) = c (σ 2) + u}`; the count is
usable only when the plane is in general position with respect to the knot `K` inside the box:

* every meeting of the knot with the plane inside the *closed* box happens in the *open* box (so the
  knot does not touch the plane on the box sphere, where the count of the box sphere and the count of
  the plane would interfere), and
* the meeting is *transversal* in the `σ 2`-coordinate (so that a small tilt of the plane, as in the
  tilted sweep, moves each crossing by a controlled amount, and the visits of the knot to a thin
  slab are exactly the crossings).

`Work.Drive.Mono.CutTransverse` is that condition.  Almost every level `u` satisfies it, provided the
knot meets the box sphere in finitely many parameters — which is exactly the crux's count `hS`.  The
proof is 1-dimensional Sard (`Work.Sweep.AeTransverseCoord.ae_transverse_coord`) for the derivative
part, and the finiteness of the box-sphere trace for the boundary part.
-/

open LeanEval.KnotTheory.PardonDistortion
open MeasureTheory Set
open scoped ENNReal Topology

namespace Work.Drive.Mono

noncomputable section

/-- **The plane level `u` is cut-transverse.**  Every meeting of the knot with the cutting plane
`{y (σ 2) = c (σ 2) + u}` inside the closed box `closure PBox s c σ` happens at a point of the open
box, transversally in the `σ 2`-coordinate. -/
def CutTransverse (K : Knot) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) : Prop :=
  ∀ t : ℝ, K.curve t ∈ closure (Submission.PBox s c σ) → (K.curve t) (σ 2) = c (σ 2) + u →
    K.curve t ∈ Submission.PBox s c σ ∧
      deriv (fun r : ℝ => (K.curve r) (σ 2)) t ≠ 0

end

end Work.Drive.Mono
