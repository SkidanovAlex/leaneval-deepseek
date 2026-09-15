import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Geometry.Manifold.ChartedSpace

namespace Commons.Analysis.Complex.ChartedSpace

open Filter Metric Set
open scoped Topology

/-- **Analyticity of a locally uniform limit on an open set.**  Let `X` be a `ℂ`-charted space, `U`
an open (implicitly, via the chart balls hypothesis) set, and `F : ℕ → X → ℂ` a family which in the
preferred chart at every point of `U` is analytic on some chart ball around that point (the
hypothesis `hball`).  If `F` converges locally uniformly to `g` on `U`, then `g` is analytic in the
preferred chart at every point of `U`.

Proof: at a point `x ∈ U`, `hball` provides a ball `Metric.ball ((chartAt ℂ x) x) ρ` inside the chart
target and whose `(chartAt ℂ x).symm`-image lies in `U`, on which every `F n` is analytic.  Because
`(chartAt ℂ x).symm` is continuous and maps this ball into `U`, the locally uniform convergence on
`U` pulls back to locally uniform convergence of `F n ∘ (chartAt ℂ x).symm` to
`g ∘ (chartAt ℂ x).symm` on the ball.  Weierstrass' theorem gives differentiability of the limit on
the open ball, hence analyticity at the centre. -/
theorem analyticAt_comp_chart_symm_of_tendstoLocallyUniformlyOn_of_isOpen {X : Type*}
    [TopologicalSpace X] [ChartedSpace ℂ X] {U : Set X} {F : ℕ → X → ℂ} {g : X → ℂ}
    (hball : ∀ x ∈ U, ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball ((chartAt ℂ x) x) ρ ⊆ (chartAt ℂ x).target ∧
      (chartAt ℂ x).symm '' Metric.ball ((chartAt ℂ x) x) ρ ⊆ U ∧
      (∀ n, ∀ z ∈ Metric.ball ((chartAt ℂ x) x) ρ, AnalyticAt ℂ (F n ∘ (chartAt ℂ x).symm) z))
    (hconv : TendstoLocallyUniformlyOn F g Filter.atTop U) :
    ∀ x ∈ U, AnalyticAt ℂ (g ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) := by
  intro x hx
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ x
  obtain ⟨ρ, hρpos, hρtgt, hρU, hρana⟩ := hball x hx
  -- Transport the locally uniform convergence back along the continuous map `e.symm`.
  have hcont : ContinuousOn e.symm (Metric.ball (e x) ρ) := e.continuousOn_symm.mono hρtgt
  have hmap : MapsTo e.symm (Metric.ball (e x) ρ) U := fun z hz => hρU ⟨z, hz, rfl⟩
  have hLU : TendstoLocallyUniformlyOn (fun n => F n ∘ e.symm) (g ∘ e.symm) Filter.atTop
      (Metric.ball (e x) ρ) :=
    hconv.comp e.symm hmap hcont
  -- Each member of the composed family is differentiable on the open ball.
  have hdiff : ∀ᶠ n in Filter.atTop,
      DifferentiableOn ℂ (fun z => F n (e.symm z)) (Metric.ball (e x) ρ) :=
    Filter.Eventually.of_forall fun n z hz =>
      (hρana n z hz).differentiableAt.differentiableWithinAt
  -- Weierstrass' theorem: the limit is differentiable (hence analytic) on the open ball.
  have hd : DifferentiableOn ℂ (fun z => g (e.symm z)) (Metric.ball (e x) ρ) :=
    hLU.differentiableOn hdiff Metric.isOpen_ball
  have hball_mem : Metric.ball (e x) ρ ∈ 𝓝 (e x) := Metric.ball_mem_nhds (e x) hρpos
  have hev : ∀ᶠ z in 𝓝 (e x), DifferentiableAt ℂ (fun z => g (e.symm z)) z := by
    filter_upwards [hball_mem] with z hz
    exact (hd z hz).differentiableAt (Metric.isOpen_ball.mem_nhds hz)
  exact Complex.analyticAt_iff_eventually_differentiableAt.mpr hev

end Commons.Analysis.Complex.ChartedSpace
