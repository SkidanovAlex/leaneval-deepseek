/-
# The cusp chart of `M̄` is an open embedding (the field `mbarLow_isEmbedding` of `CuspGlueData`)

`Work.Cusp.CuspGlueData.mbarLow_isEmbedding` asks that the cusp chart of the hyperbolic piece,
restricted to the part of a collar box that lies below the ceiling, be an **open embedding** (a
chart).  This file derives it from the three fields already proved for the concrete chart
`Work.RTOwed.mbarLow`:

* continuity (`Work.RTOwed.mbarLow_cont`),
* injectivity (`Work.RTOwed.mbarLow_inj`, box of side `≤ 1`),
* openness of the image (`Work.RTOwed.mbarLow_open`), in the strong form
  `Work.RTOwed.mbarLow_image_open`: the image of the region `chartRegion B` of **every** open `B`
  with heights `≥ 11/10` is open.

The last one upgrades "the image of the region is open" to "the image of every relatively open
subset is open" (an open map): a relatively open subset of `chartRegion (cuspChartBox v c δ)` is
`chartRegion (cuspChartBox v c δ ∩ B)` for an open `B`, and the heights are supplied by the box.
`Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap` then concludes.
-/
import Mathlib
import Submission.Work.RTOwed.mbarLow_cont
import Submission.Work.RTOwed.mbarLow_inj
import Submission.Work.RTOwed.mbarLow_open
import Submission.Work.RTOwed.cuspGlueData

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function

namespace Work.RTOwed

open Work.RTInstance

/-- **The cusp chart is an open map** on the region below the ceiling of every collar box. -/
theorem mbarLow_isOpenMap (v : Fin 5) (c : Work.Cusp.E3) (δ : ℝ) :
    IsOpenMap (fun q : {q : CuspE4 // q ∈ ChartReg v c δ} => mbarLow v q) := by
  intro U hU
  rw [isOpen_induced_iff] at hU
  obtain ⟨B, hBopen, hUB⟩ := hU
  have himg : (fun q : {q : CuspE4 // q ∈ ChartReg v c δ} => mbarLow v q) '' U
      = mbarLow v '' chartRegion (Work.Cusp.cuspChartBox v c δ ∩ B) := by
    rw [← hUB]
    ext y
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨(q : CuspE4), ⟨⟨q.2.1, hq⟩, q.2.2⟩, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨q, ⟨hq.1.1, hq.2⟩⟩, hq.1.2, rfl⟩
  rw [himg]
  refine mbarLow_image_open v (Work.Cusp.isOpen_cuspChartBox v c δ |>.inter hBopen) ?_
  intro q hq
  exact le_of_lt (by simpa only [Work.Cusp.s1] using hq.1.2.1)

/-- **The cusp chart of `M̄` is an open embedding** below the ceiling of a collar box of side
`2δ ≤ 1`: the fields `mbarLow_isEmbedding` and `mbarLow_isEmbeddingTop` of
`Work.Cusp.CuspGlueData`, for the concrete `Work.RTOwed.mbarLow`. -/
theorem mbarLow_isEmbedding (v : Fin 5) (c : Work.Cusp.E3) (δ : ℝ) (hδ : δ ≤ 1 / 2) :
    Topology.IsOpenEmbedding
        (fun q : {q : CuspE4 // q ∈ ChartReg v c δ} => mbarLow v q) ∧
      Topology.IsOpenEmbedding
        (fun q : {q : CuspE4 // q ∈ ChartRegTop v c δ} => mbarLow v q) := by
  constructor
  · refine Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap ?_ ?_
      (mbarLow_isOpenMap v c δ)
    · exact (mbarLow_cont v c δ).1.domRestrict
    · intro x y h
      exact Subtype.ext ((mbarLow_inj v c δ hδ).1 x.2 y.2 h)
  · refine Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap ?_ ?_ ?_
    · exact (mbarLow_cont v c δ).2.domRestrict
    · intro x y h
      exact Subtype.ext ((mbarLow_inj v c δ hδ).2 x.2 y.2 h)
    · intro U hU
      rw [isOpen_induced_iff] at hU
      obtain ⟨B, hBopen, hUB⟩ := hU
      have himg : (fun q : {q : CuspE4 // q ∈ ChartRegTop v c δ} => mbarLow v q) '' U
          = mbarLow v '' chartRegion (Work.Cusp.cuspBoxTop v c δ ∩ B) := by
        rw [← hUB]
        ext y
        constructor
        · rintro ⟨q, hq, rfl⟩
          exact ⟨(q : CuspE4), ⟨⟨q.2.1, hq⟩, q.2.2⟩, rfl⟩
        · rintro ⟨q, hq, rfl⟩
          exact ⟨⟨q, ⟨hq.1.1, hq.2⟩⟩, hq.1.2, rfl⟩
      rw [himg]
      refine mbarLow_image_open v (Work.Cusp.isOpen_cuspBoxTop v c δ |>.inter hBopen) ?_
      intro q hq
      exact le_of_lt (by simpa only [Work.Cusp.s1] using hq.1.2.1)

end Work.RTOwed
