import Submission.Work.PTGeometric.Lvl.Transition

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The smooth structure on the local level set

Copy of `Work.ThomBordism.Transversality.Preimage.Manifold`: the charts `chartAt S w` are pairwise
compatible, hence define a `ChartedSpace (EuclideanHalfSpace 9)` and a `C^∞` manifold structure
modelled on `𝓡∂ 9`; and a point of the level set lies on the boundary of this manifold exactly when
its underlying point lies on the boundary of `M`.

The compactness of the level set is where the closedness hypothesis on `W` enters (in the global
version it came from `coreMap⁻¹' {0}` being closed).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped Manifold Topology ContDiff
open Function Set Manifold
open ModelWithCorners
open Classical
open Work.ThomBordism.Transversality.Preimage

namespace Work.PTGeometric

noncomputable section

namespace Lvl

namespace Setup

variable {k : ℕ} (S : Setup k)

instance instChartedSpace : ChartedSpace (EuclideanHalfSpace 9) S.Pre where
  atlas := Set.range (chartAt S)
  chartAt := chartAt S
  mem_chart_source w := ⟨mem_domChartAt_source S w, chartZ_mem_chartW1 S w, S.data.mem_U w⟩
  chart_mem_atlas w := ⟨w, rfl⟩

instance instIsManifold : IsManifold (𝓡∂ 9) ∞ S.Pre := by
  refine isManifold_of_contDiffOn (𝓡∂ 9) ∞ S.Pre (fun e e' he he' => ?_)
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
  have he : chartAt S w ∈ IsManifold.maximalAtlas (𝓡∂ 9) ∞ S.Pre :=
    IsManifold.chart_mem_maximalAtlas w
  have hx : w ∈ (chartAt S w).source := mem_chart_source (EuclideanHalfSpace 9) w
  rw [mem_boundary_iff_extend_apply_coord_eq_zero (m := 9) he hx, chartAt_self_extend S w,
    chartFun_self S w, PiLp.smul_apply, Work.Surgery.e₀_apply_zero, smul_eq_mul, mul_one]
  exact chartEps_eq_zero_iff S w

/-- The level set is compact: it is a closed subset of the compact space `M`. -/
theorem isCompact_W : IsCompact S.W := S.isClosed_W.isCompact

instance instCompactSpace : CompactSpace S.Pre :=
  isCompact_iff_compactSpace.mp (isCompact_W S)

end Setup

end Lvl

end

end Work.PTGeometric
