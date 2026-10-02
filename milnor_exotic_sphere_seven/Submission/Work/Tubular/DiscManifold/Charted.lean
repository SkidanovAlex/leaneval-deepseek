import Submission.Work.Tubular.DiscManifold.Transition

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-!
# The normal disc bundle as a smooth manifold with boundary

This file assembles the `discChart`s of `ChartCont.lean` and the transition smoothness of
`Transition.lean` into the `ChartedSpace`/`IsManifold` structure of the normal disc bundle
`D_ε(ν)` of an embedding `E : V ↪ ℝ^{8+k}`, modelled on the product
`ℝ⁸ × Half (k-1)` (the half-space model is obtained from this one in `Manifold.lean`).
-/

open scoped Manifold ContDiff Topology InnerProduct InnerProductSpace
open Function Filter
open OpenPartialHomeomorph

open Work.ThomBordism.PontryaginThom (EmbeddingData CoverIdx coverBaseSet coverIndexAt
  mem_coverBaseSet_indexAt)

namespace Work.Tubular

open Work.ThomBordism Work.ThomBordism.PontryaginThom Work.SignatureBordism

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ} [NeZero k] {ε : ℝ}

/-- **The charted space structure on the normal disc bundle** `D_ε(ν)`, modelled on
`ℝ⁸ × Half (k-1)`: the charts are the `discChart C p`. -/
noncomputable def discChartedSpace {E : EmbeddingData V (8 + k)} (C : TubeChart E ε) :
    ChartedSpace (Euc 8 × Half (k - 1)) (NormalDiscSub E ε) where
  atlas := Set.range (discChart C ·)
  chartAt := discChart C
  mem_chart_source p := by
    refine (mem_chartSource_iff C p).mpr
      ⟨mem_coverBaseSet_discPiece p, mem_chart_source (Euc 8) (NormalTotal.proj p.1), ?_⟩
    refine ((DiscManifold.ballChartAmb_spec (k - 1) (chartFibPt C p)).2
      (ballVecI C (discPiece p) p) (mem_ball_ballVecI (mem_coverBaseSet_discPiece p))).mp ?_
    rw [discPt_of_mem (k - 1) (mem_ball_ballVecI (mem_coverBaseSet_discPiece p))]
    exact mem_chart_source (Half (k - 1)) (chartFibPt C p)
  chart_mem_atlas p := ⟨p, rfl⟩

/-- **The normal disc bundle is a `C¹` manifold with boundary** for the product model
`ℝ⁸ × Half (k-1)`. -/
theorem disc_isManifold {E : EmbeddingData V (8 + k)} (C : TubeChart E ε) :
    letI := discChartedSpace C
    IsManifold (Iprod k) 1 (NormalDiscSub E ε) := by
  letI := discChartedSpace C
  refine isManifold_of_contDiffOn (Iprod k) 1 (NormalDiscSub E ε) ?_
  intro e e' he he'
  rcases he with ⟨p, rfl⟩
  rcases he' with ⟨q, rfl⟩
  exact transitionSmooth C p q

end

end Work.Tubular
