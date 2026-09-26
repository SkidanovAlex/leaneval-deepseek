import Submission.Work.Step2.Spheres
import Submission.Work.Topology.SphereSlicing.All
import Submission.Work.Step2.closedBox_subset_closure_PBox

/-!
# The box as a solid: open box, closed box, and the solid swept by the family

Pardon's family of spheres is conveniently presented by the *solid* bodies it bounds: the region cut
out of the surface at time `t` is `F ∩ int(S_t)` where `S_t` is the solid.  The workspace's
`Work.SurgeryInvariance.SphereSweep` takes this reading (`region t = P.carrier ∩ interior (S t)`, so
`S t` is the solid body).

For the box this module records the two elementary facts which make the *constant* family available
as a witness:

* `closure_PBox_eq` — the closure of the open box is the closed box `{boxNorm ≤ s}`;
* `interior_closure_PBox_eq` — the interior of the closed box is the open box, so the solid body
  `closure (PBox s c σ)` cuts out exactly the region inside the box.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Step2

noncomputable section

/-- The centre of the box is in the box. -/
theorem center_mem_PBox {s : ℝ} (hs : 0 < s) (c : R3) (σ : Equiv.Perm (Fin 3)) :
    c ∈ Submission.PBox s c σ := by
  rw [Submission.mem_PBox]
  intro i
  simpa using mul_pos (Submission.boxSide_pos i) hs

/-- **The closure of the open box is the closed box.** -/
theorem closure_PBox_eq {s : ℝ} (hs : 0 < s) (c : R3) (σ : Equiv.Perm (Fin 3)) :
    closure (Submission.PBox s c σ) = {y : R3 | Submission.boxNorm c σ y ≤ s} := by
  refine Subset.antisymm ?_ (closedBox_subset_closure_PBox hs c σ)
  have hclosed : IsClosed {y : R3 | Submission.boxNorm c σ y ≤ s} :=
    isClosed_le (Work.Topology.SphereSlicing.boxNorm_continuous c σ) continuous_const
  refine closure_minimal (fun y hy => ?_) hclosed
  exact le_of_lt ((Submission.mem_PBox_iff s c σ y).mp hy)

/-- **The interior of the closed box is the open box.**  This is the convexity of the box: the
interior of the closure of a convex set with nonempty interior is its interior. -/
theorem interior_closure_PBox_eq {s : ℝ} (hs : 0 < s) (c : R3) (σ : Equiv.Perm (Fin 3)) :
    interior (closure (Submission.PBox s c σ)) = Submission.PBox s c σ := by
  have hopen := Work.Topology.SphereSlicing.isOpen_PBox s c σ
  rw [(Work.Topology.SphereSlicing.convex_PBox s c σ).interior_closure_eq_interior_of_nonempty_interior
    ⟨c, by rw [hopen.interior_eq]; exact center_mem_PBox hs c σ⟩, hopen.interior_eq]

end

end Work.Step2
