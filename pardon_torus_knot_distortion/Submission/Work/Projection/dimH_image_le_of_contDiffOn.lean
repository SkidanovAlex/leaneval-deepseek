import Mathlib

namespace Work.Projection

open scoped Manifold ContDiff
open Topology MeasureTheory

/-- The image of a set under a map which is `C^1` on an open set `U` containing it has
Hausdorff dimension at most the dimension of the source. -/
theorem dimH_image_le_of_contDiffOn {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} (hU : IsOpen U) {g : E → F} (hg : ContDiffOn ℝ 1 g U) {s : Set E}
    (hs : s ⊆ U) : dimH (g '' s) ≤ Module.finrank ℝ E := by
  calc dimH (g '' s) ≤ dimH s :=
        dimH_image_le_of_locally_lipschitzOn fun x hx =>
          have hxU : x ∈ U := hs hx
          have hat : ContDiffAt ℝ 1 g x := hg.contDiffAt (hU.mem_nhds hxU)
          let ⟨K, t, ht, hK⟩ := hat.exists_lipschitzOnWith
          ⟨K, t, nhdsWithin_le_nhds ht, hK⟩
    _ ≤ dimH (Set.univ : Set E) := dimH_mono (Set.subset_univ s)
    _ = Module.finrank ℝ E := Real.dimH_univ_eq_finrank E

end Work.Projection
