import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The total space of a vector bundle core over a locally compact base is locally compact

Let `Z` be a `VectorBundleCore ℝ B F ι` with locally compact base `B` and
finite-dimensional real fibre `F`.  Each local trivialization `Z.localTriv i` is an open
partial homeomorphism from the total space `Z.TotalSpace` onto the open subset
`Z.baseSet i ×ˢ univ` of `B × F`, and its source `Z.proj ⁻¹' Z.baseSet i` is an open
neighbourhood of any point of the total space lying over `Z.baseSet i`.  Hence the total
space is a charted space with model `B × F`.  Since `F` is finite-dimensional, it is
locally compact, so `B × F` is locally compact, and a charted space over a locally
compact model is locally compact.
-/

namespace Work.Topology

open Bundle

/-- The total space of a vector bundle core over a locally compact base, with
finite-dimensional fibre, is locally compact. -/
theorem VectorBundleCoreTotalSpaceLocallyCompact {B F ι : Type*} [TopologicalSpace B]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [LocallyCompactSpace B]
    (Z : VectorBundleCore ℝ B F ι) : LocallyCompactSpace Z.TotalSpace := by
  refine @ChartedSpace.locallyCompactSpace (B × F) Z.TotalSpace _ _
    { atlas := Set.range fun i : ι => (Z.localTriv i).toOpenPartialHomeomorph
      chartAt := fun p => (Z.localTriv (Z.indexAt p.1)).toOpenPartialHomeomorph
      mem_chart_source := fun p => Z.mem_baseSet_at p.1
      chart_mem_atlas := fun p => ⟨Z.indexAt p.1, rfl⟩ }
    inferInstance

end Work.Topology
