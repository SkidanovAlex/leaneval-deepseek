import Mathlib
import Submission.Work.Geo.Radial.ChartImage

namespace Work.Geo.Radial

open Set Metric
open Work.Geo.Radial

/-- The chart map of a cube chart sends open subsets of the open unit cube to open subsets
of `M`. -/
theorem isOpen_image_of_subset {n : ℕ} {M : Type*} [TopologicalSpace M]
    (c : PL.CubeChart n M) {V : Set (PL.E n)} (hV : IsOpen V)
    (hVs : V ⊆ PL.openCube (n := n) 1) : IsOpen (c.toFun '' V) := by
  have hW : IsOpen ((Subtype.val ⁻¹' V) : Set (PL.openCube (n := n) 1)) :=
    hV.preimage continuous_subtype_val
  have h := (c.emb.isOpen_iff_image_isOpen).1 hW
  rwa [Set.image_domRestrict, inter_eq_self_of_subset_left hVs] at h

end Work.Geo.Radial
