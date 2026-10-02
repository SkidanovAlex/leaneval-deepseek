import Mathlib
import Submission.Work.RatHurewicz.subsingleton_relPi_of_compressRel_range
import Submission.Work.Serre.AttachCompress.Assemble

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Serre

open scoped Topology unitInterval

open Work.RatHurewicz

/-!
# Compression for cell attachments: the relative homotopy groups of `Y ↪ Y ∪ (n+2)-cells` vanish up to `n+1`

`Work.RatHurewicz.attachCells n Y ι f` is `Y` with `(n+2)`-cells glued on along maps
`f i : S^{n+1} → Y`, and `Work.RatHurewicz.RelHomotopyGroup i a₀ j` is `π_j` of the homotopy fibre
of `i : A → X`; with `i = attachIncl` it is the classical `π_{j+1}(Y', Y)`.  Content: attaching
cells of dimension `n+2` does not change `π_j` for `j ≤ n`; equivalently the pair `(Y', Y)` is
`(n+1)`-connected.

The compression statement (`∀ d ≤ n+1`, every map of pairs `(I^d, ∂I^d) → (Y', range attachIncl)`
is homotopic relative to the boundary into the range) is
`Work.Serre.AttachCompress.compression`: the general-position step is
`Work.AttachPush.exists_homotopy_avoids_cellOrigins` and the push-off step is
`Work.RatHurewicz.exists_pushOff_homotopy`.  The vanishing of the relative groups follows from the
compression by `Work.RatHurewicz.subsingleton_relPi_of_compressRel_range`.
-/

theorem serreAttachCompress :
    ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
      (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (y₀ : Y),
      ∀ j : ℕ, j ≤ n →
        Subsingleton (Work.RatHurewicz.RelHomotopyGroup
          (Work.RatHurewicz.attachIncl n Y ι f) y₀ j) := by
  intro n Y _ ι f y₀ j hj
  exact Work.RatHurewicz.subsingleton_relPi_of_compressRel_range n Y ι f y₀
    (Work.Serre.AttachCompress.compression n Y ι f) j hj

end Work.Serre
