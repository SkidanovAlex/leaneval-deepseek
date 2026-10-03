/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORP311 area

# The window kernel `Ewin n N t m Z` carries an orthogonal projection

`Work.ORP311.P311.Ewin n N t m Z` is cut out of `HSum n = ⊕_{i : Fin n} ℓ²(G)` by

* the closed subspace `ell2Sub n (window N t m)` (the closed span of the `δ`-directions of the
  Følner window `X_m`), and
* the submodule `⨅_{j ∈ (-m, m]} ker (blk_j ∘ Z)` — an intersection of kernels of continuous
  linear maps, hence closed.

Both pieces are closed in the complete space `HSum n`, so their intersection is closed, and a
closed subspace of a complete inner product space admits an orthogonal projection
(`Submodule.HasOrthogonalProjection.ofCompleteSpace`).
-/
import Mathlib
import Submission.Work.ORP311.P311Defs

namespace Work.ORP311

/-- **The window kernel is closed.**  It is the intersection of the closed subspace
`ell2Sub n (window N t m)` (a topological closure) with the intersection over
`-(m : ℤ) < j ≤ m` of the kernels of the continuous linear maps `blk n N t j ∘L Z`. -/
theorem isClosed_Ewin {G : Type*} [Group G] [Countable G] [MeasurableSpace G]
    [MeasurableSingletonClass G] [MeasurableMul G] (n : ℕ) (N : Subgroup G) (t : G) (m : ℕ)
    (Z : Work.ORVonNeumann.Rep.HSum (G := G) n →L[ℂ] Work.ORVonNeumann.Rep.HSum (G := G) n) :
    IsClosed ((Work.ORP311.P311.Ewin n N t m Z : Submodule ℂ
      (Work.ORVonNeumann.Rep.HSum (G := G) n)) : Set (Work.ORVonNeumann.Rep.HSum (G := G) n)) := by
  rw [Work.ORP311.P311.Ewin, Submodule.coe_inf]
  refine IsClosed.inter ?_ ?_
  · exact Submodule.isClosed_topologicalClosure _
  · rw [Submodule.coe_iInf]
    refine isClosed_iInter fun j => ?_
    rw [Submodule.coe_iInf]
    refine isClosed_iInter fun _ => ?_
    exact ContinuousLinearMap.isClosed_ker _

theorem Ewin_hasOrthogonalProjection {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] (n : ℕ) (N : Subgroup G) (t : G) (m : ℕ) (Z : Work.ORVonNeumann.Rep.HSum (G := G) n →L[ℂ] Work.ORVonNeumann.Rep.HSum (G := G) n) : (Work.ORP311.P311.Ewin n N t m Z).HasOrthogonalProjection := by
  have hcomp : CompleteSpace ↥(Work.ORP311.P311.Ewin n N t m Z) :=
    (isClosed_Ewin n N t m Z).completeSpace_coe
  exact Submodule.HasOrthogonalProjection.ofCompleteSpace _

end Work.ORP311
