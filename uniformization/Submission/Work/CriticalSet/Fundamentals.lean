import Submission.Work.CriticalSet.Defs
import Submission.Commons.Geometry.Manifold.chart_transition_analyticOnNhd
import Submission.Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn

/-!
# Fundamentals for the regular-level-set toolkit

Three elementary facts:

* `Work.CriticalSet.chart_transition_deriv_ne_zero` — a chart transition of a one-dimensional
  complex manifold has non-vanishing complex derivative.
* `Work.CriticalSet.fderiv_re_eq_zero_iff` — for a complex analytic `F`, the real derivative of
  `w ↦ (F w).re` vanishes at `z` exactly when the complex derivative `F' z` does.  (This is the
  bridge between "vanishing gradient of a harmonic function" and "zero of the derivative of its
  holomorphic companion".)
* `Work.CriticalSet.eventually_deriv_ne_zero_of_not_eventually_re_eq` — the zeros of `F'` are
  isolated unless the real part of `F` is locally constant.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

noncomputable section

open Filter Set
open Classical

namespace Work.CriticalSet

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **Chart transitions have non-vanishing derivative.**  If `x` lies in the source of the chart at
`y`, then the transition `(chartAt ℂ y)⁻¹ ∘ chartAt ℂ x` has non-zero complex derivative at
`(chartAt ℂ y) x`. -/
theorem chart_transition_deriv_ne_zero {x y : X} (hx : x ∈ (chartAt ℂ y).source) :
    deriv (fun w : ℂ => (chartAt ℂ x) ((chartAt ℂ y).symm w)) ((chartAt ℂ y) x) ≠ 0 := by
  have hzx : (chartAt ℂ y).symm ((chartAt ℂ y) x) = x := (chartAt ℂ y).left_inv hx
  have hmem : (chartAt ℂ y) x ∈ ((chartAt ℂ y).symm ≫ₕ chartAt ℂ x).source := by
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨(chartAt ℂ y).map_source hx, ?_⟩
    simp only [Set.mem_preimage, hzx]
    exact mem_chart_source ℂ x
  obtain ⟨r, hr, hrsub⟩ :=
    Metric.isOpen_iff.mp ((chartAt ℂ y).symm ≫ₕ chartAt ℂ x).open_source _ hmem
  have hana := (Commons.Geometry.Manifold.chart_transition_analyticOnNhd y x) _ hmem
  refine Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn hr ?_ ?_
  · exact hana
  intro u hu v hv huv
  have hu' := hrsub (Metric.mem_ball.mp hu)
  have hv' := hrsub (Metric.mem_ball.mp hv)
  simp only [OpenPartialHomeomorph.trans_source, Set.mem_inter_iff, Set.mem_preimage,
    OpenPartialHomeomorph.symm_source] at hu' hv'
  have h1 : (chartAt ℂ y).symm u = (chartAt ℂ y).symm v :=
    (chartAt ℂ x).injOn hu'.2 hv'.2 huv
  exact (chartAt ℂ y).symm.injOn hu'.1 hv'.1 h1

end Work.CriticalSet

section PureComplex

open Complex

/-- For a complex analytic `F`, the real derivative of `w ↦ (F w).re` vanishes at `z` if and only
if the complex derivative of `F` at `z` vanishes. -/
theorem Work.CriticalSet.fderiv_re_eq_zero_iff {F : ℂ → ℂ} {z : ℂ} (hF : AnalyticAt ℂ F z) :
    fderiv ℝ (fun w => (F w).re) z = 0 ↔ deriv F z = 0 := by
  have hfd : HasFDerivAt F (ContinuousLinearMap.toSpanSingleton ℂ (deriv F z)) z :=
    hF.differentiableAt.hasDerivAt.hasFDerivAt
  have hfdR : HasFDerivAt F
      ((ContinuousLinearMap.toSpanSingleton ℂ (deriv F z)).restrictScalars ℝ) z :=
    hfd.restrictScalars ℝ
  have hcomp : HasFDerivAt (fun w : ℂ => (F w).re)
      (Complex.reCLM.comp ((ContinuousLinearMap.toSpanSingleton ℂ (deriv F z)).restrictScalars ℝ)) z :=
    (ContinuousLinearMap.hasFDerivAt Complex.reCLM).comp z hfdR
  rw [hcomp.fderiv]
  constructor
  · intro h
    have h1 : (deriv F z).re = 0 := by
      have hg := congrArg (fun (g : ℂ →L[ℝ] ℝ) => g (1 : ℂ)) h
      simpa [ContinuousLinearMap.comp_apply] using hg
    have h2 : (deriv F z).im = 0 := by
      have hg := congrArg (fun (g : ℂ →L[ℝ] ℝ) => g Complex.I) h
      simpa [ContinuousLinearMap.comp_apply, Complex.mul_re] using hg
    exact Complex.ext h1 h2
  · intro h
    rw [h]
    ext w
    simp

/-- The zeros of the derivative of a complex analytic function are isolated, unless the real part
of the function is locally constant. -/
theorem Work.CriticalSet.eventually_deriv_ne_zero_of_not_eventually_re_eq {F : ℂ → ℂ} {z : ℂ}
    (hF : AnalyticAt ℂ F z) (h : ¬ ∀ᶠ w in 𝓝 z, (F w).re = (F z).re) :
    ∀ᶠ w in 𝓝[≠] z, deriv F w ≠ 0 := by
  have hne : ¬ (deriv F =ᶠ[𝓝 z] 0) := by
    intro hz0
    have hall : ∀ᶠ w in 𝓝 z, deriv F w = 0 ∧ AnalyticAt ℂ F w :=
      hz0.and ((isOpen_analyticAt ℂ F).mem_nhds hF)
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hall
    have hconst : ∀ w ∈ Metric.ball z r, F w = F z := fun w hw =>
      IsOpen.is_const_of_deriv_eq_zero Metric.isOpen_ball (convex_ball z r).isPreconnected
        (fun v hv => ((hball (Metric.mem_ball.mp hv)).2).differentiableAt.differentiableWithinAt)
        (fun v hv => (hball (Metric.mem_ball.mp hv)).1) hw (Metric.mem_ball_self hr)
    exact h (Filter.eventually_of_mem (Metric.ball_mem_nhds z hr) (fun w hw => by rw [hconst w hw]))
  rcases (hF.deriv.eventually_eq_zero_or_eventually_ne_zero) with h0 | h0
  · exact absurd h0 hne
  · exact h0

end PureComplex
