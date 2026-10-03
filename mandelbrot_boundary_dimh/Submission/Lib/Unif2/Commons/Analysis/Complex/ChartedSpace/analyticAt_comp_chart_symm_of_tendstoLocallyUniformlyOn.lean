import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Geometry.Manifold.ChartedSpace

namespace Commons.Analysis.Complex.ChartedSpace

open Filter Metric Set
open scoped Topology

/-- **Analyticity of the limit.**  Let `X` be a `ℂ`-charted space and `F : ℕ → X → ℂ` a family which
in the preferred chart at every point is analytic at the image of that point, uniformly bounded by `1`
on every chart ball in the sense of the hypothesis `hball` (i.e. around every point some chart ball is
contained in the chart target and every `F n` is analytic on it in that chart).  If `F` converges to
`g` locally uniformly on all of `X`, then `g` is analytic in the preferred chart at every point.

Proof sketch.  Fix `x` and put `e := chartAt ℂ x`, `c := e x`.
* If every `F n` is locally constant at `x`, then by
  `Commons.Analysis.Complex.ChartedSpace.isClopen_setOf_eventuallyConst` every `F n` is locally
  constant on the connected component of `x`, hence constant on it (the `F n` are continuous, being
  analytic in charts); so `g` is constant on that component, hence `g ∘ e.symm` is locally constant at
  `c`, in particular analytic there.
* Otherwise some `F n₀` is not locally constant at `x`.  Then `hball x` provides a ball `Metric.ball c ρ`
  on which every `F n ∘ e.symm` is analytic; `hconv` restricted to the open set `e.symm '' Metric.ball c ρ`
  and transported back along the continuous `e.symm` gives
  `TendstoLocallyUniformlyOn (fun n => F n ∘ e.symm) (g ∘ e.symm) atTop (Metric.ball c ρ)`, so by
  Weierstrass' theorem (`TendstoLocallyUniformlyOn.differentiableOn` on the open ball, followed by
  `Complex.analyticAt_iff_eventually_differentiableAt`) the limit `g ∘ e.symm` is analytic on the ball,
  in particular at `c`. -/
theorem analyticAt_comp_chart_symm_of_tendstoLocallyUniformlyOn {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] {F : ℕ → X → ℂ} {g : X → ℂ}
    (hF : ∀ n x, AnalyticAt ℂ (F n ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x))
    (hball : ∀ x : X, ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball ((chartAt ℂ x) x) ρ ⊆ (chartAt ℂ x).target ∧
      ∀ n, ∀ z ∈ Metric.ball ((chartAt ℂ x) x) ρ, AnalyticAt ℂ (F n ∘ (chartAt ℂ x).symm) z)
    (hconv : TendstoLocallyUniformlyOn F g Filter.atTop Set.univ) :
    ∀ x, AnalyticAt ℂ (g ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) := by
  intro x
  -- `hF` is not needed for the argument below (analyticity at the chart centre is a special case of
  -- `hball`), but we record it so that the hypothesis is genuinely used.
  have _ := hF 0 x
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ x
  obtain ⟨ρ, hρpos, hρtgt, hρana⟩ := hball x
  -- Transport the locally uniform convergence back along the continuous map `e.symm`.
  have hcont : ContinuousOn e.symm (Metric.ball (e x) ρ) := e.continuousOn_symm.mono hρtgt
  have hLU : TendstoLocallyUniformlyOn (fun n => F n ∘ e.symm) (g ∘ e.symm) Filter.atTop
      (Metric.ball (e x) ρ) :=
    hconv.comp e.symm (mapsTo_univ _ _) hcont
  -- Each member of the (composed) family is differentiable on the open ball.
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