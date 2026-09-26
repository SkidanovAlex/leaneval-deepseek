import Mathlib
import Submission.Work.InnermostDisk.Slicing

/-!
# A slicing of a sphere covers the surface's intersection with it

`Work.InnermostDisk.SphereSlicing` records a family of pairwise disjoint simple closed curves of the
surface lying in a sphere `S` (`mem`), each bounding an embedded disc in `S`, nested
(`inside`, `inside_subset`), with the interiors of the discs meeting the surface only along curves
(`covers_interior`), and — the field used here — `covers`: every *loop* of the surface contained in
`S` lies in one of the curves.

The field `covers` applies in particular to a **constant** loop at a point `z ∈ S ∩ carrier`: such a
loop is a `ClosedCurve` (it is continuous, periodic and takes its value in the carrier), so
`covers` produces a curve of the slicing passing through `z`.  Consequently

  `P.carrier ∩ S ⊆ ⋃ i, Set.range (h.c i).γ`

with no transversality assumption whatsoever.  This is what makes the trace of a level of the tilted
sweep a union of curves *at the box sphere*: a point `z` of the surface where the surface touches the
box from the outside is still on a slicing curve, and since the slicing curves are `IsSimple` (hence
nonconstant), such a tangency cannot occur at all.

The statement is about the structure `SphereSlicing` only, so it applies to every sphere for which a
slicing is available (`Work.BoxShrink.SlicedSphere`), for instance the box sphere of the crux.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.InnermostDisk

noncomputable section

/-- The **constant closed curve** at a point of the surface. -/
def constClosedCurve {P : Work.CoreTopology.ParamTorus} (z : R3) (hz : z ∈ P.carrier) :
    Work.CoreTopology.ClosedCurve P where
  γ := fun _ => z
  cont := continuous_const
  periodic := fun _ => rfl
  mem := fun _ => hz

@[simp] theorem constClosedCurve_apply {P : Work.CoreTopology.ParamTorus} (z : R3)
    (hz : z ∈ P.carrier) (t : ℝ) : (constClosedCurve z hz).γ t = z := rfl

/-- **A slicing of a sphere covers the surface's intersection with it.** -/
theorem carrier_inter_subset_iUnion_range_of_sphereSlicing {P : Work.CoreTopology.ParamTorus}
    {S : Set R3} (h : Work.InnermostDisk.SphereSlicing P S) :
    P.carrier ∩ S ⊆ ⋃ i, Set.range (h.c i).γ := by
  intro z hz
  obtain ⟨hzc, hzS⟩ := hz
  obtain ⟨i, hi⟩ := h.covers (constClosedCurve z hzc) (fun _ => hzS)
  exact Set.mem_iUnion.mpr ⟨i, hi ⟨0, rfl⟩⟩

end

end Work.InnermostDisk
