import Submission.Work.ThomBordism.Transversality.Preimage.Transition

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The smooth structure on the transverse preimage

The charts `chartAt S w` of `Chart.lean` are pairwise compatible: their transitions are the ambient
changes of charts in the normal-form coordinates (`contDiffOn_chartAt_trans`).  Hence they define a
`ChartedSpace (EuclideanHalfSpace 9)` structure on `S.Pre`, and the compatibility makes
`S.Pre` a `C^∞` manifold with boundary modelled on `𝓡∂ 9`.

The last result, `mem_boundary_iff`, identifies the boundary of this manifold with the end preimage
of the core: a point of `S.Pre` lies on the boundary exactly when its underlying point in `M` is on
the boundary of `M` (and hence, being in the preimage of the core, in the end preimage).
-/

open scoped Manifold Topology ContDiff
open Function Set Manifold
open ModelWithCorners
open Classical

namespace Work.ThomBordism.Transversality.Preimage

noncomputable section

namespace CoreSetup

variable {k : ℕ} (S : CoreSetup k)

instance instChartedSpace : ChartedSpace (EuclideanHalfSpace 9) S.Pre where
  atlas := Set.range (chartAt S)
  chartAt := chartAt S
  mem_chart_source w := ⟨mem_domChartAt_source S w, chartZ_mem_chartW1 S w⟩
  chart_mem_atlas w := ⟨w, rfl⟩

instance instIsManifold : IsManifold (𝓡∂ 9) smoothHeight S.Pre := by
  refine isManifold_of_contDiffOn (𝓡∂ 9) smoothHeight S.Pre (fun e e' he he' => ?_)
  obtain ⟨w, rfl⟩ := he
  obtain ⟨w', rfl⟩ := he'
  exact contDiffOn_chartAt_trans S w w'

theorem chartFun_self (w : S.Pre) : chartFun S w w = chartEps S w • Work.Surgery.e₀ 8 := by
  show chartBeta S w ((S.domChartAt w).extend (𝓡∂ ((8 + k) + 1)) w.1
      - (S.domChartAt w).extend (𝓡∂ ((8 + k) + 1)) w.1) + chartEps S w • Work.Surgery.e₀ 8
    = chartEps S w • Work.Surgery.e₀ 8
  rw [sub_self, map_zero, zero_add]

theorem chartEps_eq_zero_iff (w : S.Pre) :
    chartEps S w = 0 ↔ w.1 ∈ (𝓡∂ ((8 + k) + 1)).boundary S.M := by
  refine ⟨fun h => ?_, chartEps_eq_zero S w⟩
  by_contra hc
  exact absurd h (ne_of_gt (chartEps_pos S w hc))

theorem chartAt_self_extend (w : S.Pre) :
    ((chartAt S w).extend (𝓡∂ 9)) w = chartFun S w w := by
  rw [OpenPartialHomeomorph.extend_coe, Function.comp_apply,
    chartAt_apply_of_mem S w (mem_chart_source (EuclideanHalfSpace 9) w),
    modelWithCornersEuclideanHalfSpace_apply]

theorem mem_boundary_iff (w : S.Pre) :
    w ∈ (𝓡∂ 9).boundary S.Pre ↔ w.1 ∈ (𝓡∂ ((8 + k) + 1)).boundary S.M := by
  have he : chartAt S w ∈ IsManifold.maximalAtlas (𝓡∂ 9) smoothHeight S.Pre :=
    IsManifold.chart_mem_maximalAtlas w
  have hx : w ∈ (chartAt S w).source := mem_chart_source (EuclideanHalfSpace 9) w
  rw [mem_boundary_iff_extend_apply_coord_eq_zero (m := 9) he hx, chartAt_self_extend S w,
    chartFun_self S w, PiLp.smul_apply, Work.Surgery.e₀_apply_zero, smul_eq_mul, mul_one]
  exact chartEps_eq_zero_iff S w

theorem isCompact_pre : IsCompact (S.F ⁻¹' S.X.core) := by
  have hset : S.F ⁻¹' S.X.core = {x : S.M | S.coreMap x = 0} := rfl
  rw [hset]
  exact (isClosed_eq S.contMDiff_coreMap.continuous continuous_const).isCompact

instance instCompactSpace : CompactSpace S.Pre :=
  isCompact_iff_compactSpace.mp (isCompact_pre S)

end CoreSetup

end

end Work.ThomBordism.Transversality.Preimage
