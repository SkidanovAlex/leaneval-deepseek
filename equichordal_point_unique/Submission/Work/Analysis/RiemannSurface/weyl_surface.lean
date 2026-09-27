import Mathlib
import Submission.Holomorphic
import Submission.Work.Analysis.Complex.DbarCauchy.weyl_weak
import Submission.Work.Analysis.Complex.DbarCauchy.Defs

/-!
# Surface Weyl, chartwise ("rung 1" of the divisor chapter's L² route)

The plane Weyl lemma (`Work.Analysis.Complex.DbarCauchy.analyticOnNhd_of_weak_dbar_zero`) is
transferred to a Riemann surface chartwise.  The point of the transfer is that on a surface the weak
`∂̄`-equation is *stated chartwise* (there is no canonical measure on `X`, and the pairing
`∫ v ∂̄φ` is a chart-local expression anyway), so "surface Weyl" is exactly the plane lemma read in
the chart at the point under consideration — no gluing is needed at this rung.  The gluing problem
of the surface layer is elsewhere (getting a weak solution *on* `X` from the chart-local engine,
i.e. rung 2), and the *multiplicative* step needs the period/exponential-sequence argument.

Two statements:

* `weyl_surface_chart` — if the chart representative of `v` at `x` is locally `L²` and weakly
  `∂̄`-closed (test functions supported in the chart's target), then it agrees a.e. with a function
  analytic on a ball around `(chartAt ℂ x) x` inside the chart's target;
* `integral_mul_dbar_eq_of_ae_eq` — a function agreeing a.e. with an analytic function on an open set
  has the *same* `∂̄`-pairings against test functions supported there.  This is the step that lets the
  endgame replace a weak `L²` solution by its analytic/smooth representative inside every integral
  (and hence inside every sup-norm bound obtained from an `L²` bound).
-/

open MeasureTheory Set Filter
open scoped Topology Manifold

noncomputable section

namespace Work.Analysis.RiemannSurface

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]

/-- **Surface Weyl, chartwise.**  If the chart representative at `x` of `v : X → ℂ` is locally `L²`
and weakly `∂̄`-closed against test functions supported in the chart's target, then it agrees a.e.
with a function analytic on a ball around `(chartAt ℂ x) x` contained in the target. -/
theorem weyl_surface_chart {v : X → ℂ} {x : X}
    (hli : LocallyIntegrable (v ∘ (chartAt ℂ x).symm) volume)
    (hli2 : LocallyIntegrable (fun w => ‖(v ∘ (chartAt ℂ x).symm) w‖ ^ 2) volume)
    (h : ∀ φ : ℂ → ℂ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      tsupport φ ⊆ (chartAt ℂ x).target →
      ∫ w in (chartAt ℂ x).target,
        (v ∘ (chartAt ℂ x).symm) w * Work.Analysis.Complex.DbarCauchy.dbar φ w = 0) :
    ∃ (g : ℂ → ℂ) (δ : ℝ), 0 < δ ∧
      Metric.closedBall ((chartAt ℂ x) x) δ ⊆ (chartAt ℂ x).target ∧
      AnalyticOnNhd ℂ g (Metric.ball ((chartAt ℂ x) x) δ) ∧
      ∀ᵐ w ∂(volume.restrict (Metric.ball ((chartAt ℂ x) x) δ)),
        (v ∘ (chartAt ℂ x).symm) w = g w :=
  Work.Analysis.Complex.DbarCauchy.analyticOnNhd_of_weak_dbar_zero (chartAt ℂ x).open_target
    hli hli2 h ((chartAt ℂ x).map_source (mem_chart_source ℂ x))

/-- A function agreeing a.e. with an analytic function on an open set has the same `∂̄`-pairings
against test functions supported there. -/
theorem integral_mul_dbar_eq_of_ae_eq {v g : ℂ → ℂ} {U : Set ℂ}
    (hae : v =ᵐ[volume.restrict U] g) {φ : ℂ → ℂ} :
    ∫ z in U, v z * Work.Analysis.Complex.DbarCauchy.dbar φ z
      = ∫ z in U, g z * Work.Analysis.Complex.DbarCauchy.dbar φ z := by
  refine integral_congr_ae ?_
  filter_upwards [hae] with z hz
  rw [hz]

end Work.Analysis.RiemannSurface
