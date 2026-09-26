import Mathlib
import Submission.Work.PinchCounted.Counting
import Submission.Work.Topology.SphereSlicing.All

namespace Work.PinchCounted

/-- **The engine of Pardon's Lemma 2 in slice-data form.**  If `S` carries a slicing datum by the
surface `F = P.carrier`, the cut-and-paste `CleansDiscs P` holds, and `S` meets the knot `β` in
fewer than `I(F,β)` points, then every piece `Y ⊆ S` of the surface has vanishing winding span.

The innermost-disc input `CleansInSphere P S` is obtained from the slicing of `S`
(`Work.Topology.SphereSlicing.sphereSlicingOfSliceData` followed by
`Work.InnermostDisk.SphereSlicing.innermostDiscInput_of_slicing`, exactly as in
`Work.PinchCounted.cleansInSphere_of_slicing`) together with `CleansDiscs P`, and the count is
consumed by `Work.PinchCounted.windingSpan_eq_bot_of_subset_of_count`. -/
theorem windingSpan_eq_bot_of_subset_of_sliceData {P : Work.CoreTopology.ParamTorus}
    (β : Work.CoreTopology.ClosedCurve P) {S Y : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (hslice : Work.Topology.SphereSlicing.SliceData P S)
    (hcl : Work.InnermostDisk.CleansDiscs P)
    (hcount : Set.encard (Set.range β.γ ∩ S) < Work.CoreTopology.pardonsI P β) (hYS : Y ⊆ S) :
    Work.SurgeryInvariance.WindingSpan P Y = ⊥ :=
  windingSpan_eq_bot_of_subset_of_count β
    (cleansInSphere_of_slicing
      (Work.Topology.SphereSlicing.nonempty_sphereSlicing_of_sliceData hslice) hcl)
    hcount hYS

end Work.PinchCounted
