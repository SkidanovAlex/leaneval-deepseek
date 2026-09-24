import Mathlib
import Submission.Work.CriticalSet.Defs
import Submission.Work.CriticalSet.Fundamentals

namespace Work.CriticalSet

open Filter Set
open scoped Manifold ContDiff Topology

/-- **Chart independence of the critical-point condition.**

`Work.CriticalSet.IsCriticalPointAt u x` is defined by testing the vanishing of the real derivative
of the chart pullback of `u` in the *preferred* chart at `x`.  This result says that, for `u` harmonic
at `x`, one may test it in the chart at any other point `y` whose source contains `x`.

Proof strategy.  Put `z := (chartAt ℂ y) x`, `f := u ∘ (chartAt ℂ y).symm`,
`g := u ∘ (chartAt ℂ x).symm` and `T w := (chartAt ℂ x) ((chartAt ℂ y).symm w)`.  Since
`(chartAt ℂ x) ((chartAt ℂ x).symm w) = w` for `w` near `(chartAt ℂ x) x`, we have
`f =ᶠ g ∘ T` near `z`, hence by `Filter.EventuallyEq.fderiv_eq` and the chain rule
`fderiv ℝ f z = (fderiv ℝ g ((chartAt ℂ x) x)) ∘L (fderiv ℝ T z)`.  The transition `T` is complex
analytic at `z` (see `Commons.Geometry.Manifold.chart_transition_analyticOnNhd y x`) with non-zero
derivative `deriv T z ≠ 0` (`Work.CriticalSet.chart_transition_deriv_ne_zero`), so
`fderiv ℝ T z` — which is `w ↦ w * deriv T z`, the real-linear isomorphism given by multiplication by
a non-zero complex number — is surjective; and a composite `A ∘L B = 0` with `B` surjective vanishes
iff `A = 0`.  (Note `T z = (chartAt ℂ x) x` by `OpenPartialHomeomorph.left_inv`, and
`fderiv ℝ g ((chartAt ℂ x) x) = 0` is exactly `IsCriticalPointAt u x`.)

Use `hu.1.differentiableAt` (or similar) for differentiability of `g` at `(chartAt ℂ x) x`. -/
theorem criticalPoint_iff_chartAt {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {u : X → ℝ} {x y : X}
    (hxy : x ∈ (chartAt ℂ y).source) (hu : Submission.HarmonicOnXAt u x) :
    IsCriticalPointAt u x ↔ fderiv ℝ (u ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) x) = 0 := by
  classical
  -- the chart images and the chart pullbacks of `u` in the two charts
  let z : ℂ := (chartAt ℂ y) x
  let a : ℂ := (chartAt ℂ x) x
  let g : ℂ → ℝ := u ∘ (chartAt ℂ x).symm
  let f : ℂ → ℝ := u ∘ (chartAt ℂ y).symm
  -- the chart transition, from the chart at `y` to the chart at `x`
  let T : ℂ → ℂ := fun w => (chartAt ℂ x) ((chartAt ℂ y).symm w)
  have hzy : (chartAt ℂ y).symm z = x := (chartAt ℂ y).left_inv hxy
  have hTa : T z = a := by
    simp only [T, a, hzy]
  -- `z` lies in the source of the transition
  have hzsrc : z ∈ ((chartAt ℂ y).symm.trans (chartAt ℂ x)).source := by
    rw [OpenPartialHomeomorph.trans_source, Set.mem_inter_iff, Set.mem_preimage]
    exact ⟨(chartAt ℂ y).map_source hxy, by rw [hzy]; exact mem_chart_source ℂ x⟩
  -- the transition is complex analytic at `z`
  have htrans : ((chartAt ℂ y).symm.trans (chartAt ℂ x) : ℂ → ℂ) =ᶠ[𝓝 z] T := by
    filter_upwards [((chartAt ℂ y).symm.trans (chartAt ℂ x)).open_source.eventually_mem hzsrc]
      with w _
    simp only [OpenPartialHomeomorph.trans_apply, T]
  have hTana : AnalyticAt ℂ T z :=
    (AnalyticAt.congr
      ((Commons.Geometry.Manifold.chart_transition_analyticOnNhd (X := X) (x := y) (y := x)) z
        hzsrc)
      htrans)
  -- its complex derivative is non-zero
  have hderiv : deriv T z ≠ 0 := by
    have h0 := chart_transition_deriv_ne_zero (X := X) hxy
    have hlam : (fun w : ℂ => (chartAt ℂ x) ((chartAt ℂ y).symm w)) =ᶠ[𝓝 z] T := by
      filter_upwards [((chartAt ℂ y).symm.trans (chartAt ℂ x)).open_source.eventually_mem hzsrc]
        with w _
      simp only [T]
    rw [← hlam.deriv_eq]
    exact h0
  -- hence the real derivative of `T` at `z` — multiplication by that non-zero complex number — is
  -- surjective
  have hsurj : Function.Surjective (fderiv ℝ T z) := by
    have hfdT : HasFDerivAt T (ContinuousLinearMap.toSpanSingleton ℂ (deriv T z)) z :=
      hTana.differentiableAt.hasDerivAt.hasFDerivAt
    have hfdTR : HasFDerivAt T
        ((ContinuousLinearMap.toSpanSingleton ℂ (deriv T z)).restrictScalars ℝ) z :=
      hfdT.restrictScalars ℝ
    have hfT : fderiv ℝ T z
        = (ContinuousLinearMap.toSpanSingleton ℂ (deriv T z)).restrictScalars ℝ := hfdTR.fderiv
    intro w
    refine ⟨w * (deriv T z)⁻¹, ?_⟩
    rw [hfT]
    simp [ContinuousLinearMap.toSpanSingleton_apply, mul_assoc, inv_mul_cancel₀ hderiv]
  -- differentiability of the two pullbacks at the relevant points
  have hgdiff : DifferentiableAt ℝ g a := by
    have h2 : ContDiffAt ℝ 2 g a := hu.1
    exact h2.differentiableAt (by norm_num)
  have hTdiff : DifferentiableAt ℝ T z :=
    ((hTana.differentiableAt.hasDerivAt.hasFDerivAt).restrictScalars ℝ).differentiableAt
  -- `f =ᶠ g ∘ T` near `z`, because `(chartAt ℂ x) ∘ (chartAt ℂ x).symm = id` there
  have hAg : f =ᶠ[𝓝 z] g ∘ T := by
    filter_upwards [((chartAt ℂ y).symm.trans (chartAt ℂ x)).open_source.eventually_mem hzsrc]
      with w hw
    have hw2 : (chartAt ℂ y).symm w ∈ (chartAt ℂ x).source := hw.2
    simp only [f, g, T, Function.comp_apply]
    rw [(chartAt ℂ x).left_inv hw2]
  -- the chain rule
  have hchain : fderiv ℝ (g ∘ T) z = (fderiv ℝ g a).comp (fderiv ℝ T z) := by
    have hgF : HasFDerivAt g (fderiv ℝ g a) (T z) := by
      rw [hTa]
      exact hgdiff.hasFDerivAt
    exact (hgF.comp z hTdiff.hasFDerivAt).fderiv
  have hfz : fderiv ℝ f z = (fderiv ℝ g a).comp (fderiv ℝ T z) := by
    rw [hAg.fderiv_eq, hchain]
  -- the critical-point condition is the vanishing of `fderiv ℝ g a`
  show fderiv ℝ g a = 0 ↔ fderiv ℝ f z = 0
  rw [hfz]
  constructor
  · intro h
    rw [h]
    ext v
    simp
  · intro h
    ext v
    obtain ⟨w, hw⟩ := hsurj v
    have h2 := congrArg (fun (L : ℂ →L[ℝ] ℝ) => L w) h
    have h1 : (fderiv ℝ g a) ((fderiv ℝ T z) w) = 0 := by
      simpa [ContinuousLinearMap.comp_apply] using h2
    rw [← hw]
    exact h1

end Work.CriticalSet
