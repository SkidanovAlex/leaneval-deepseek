import Mathlib
import Submission.Work.TMComp.MAnalytic.deriv_bound
import Submission.Work.TMComp.MAnalytic.measurable_deriv_param

open MeasureTheory Set intervalIntegral
open scoped Interval Topology

namespace Work.TMComp.MAnalytic

/-- Core assembly: if a jointly continuous family `g : ℂ → ℝ → ℂ` whose slices are holomorphic
has, near every point, a uniform bound on the slices' derivatives over `[0,1]`, and if the
parameter derivative is measurable, then `z ↦ ∫ x in 0..1, g z x` is holomorphic. -/
private theorem integral_differentiableOn_of_bound_and_meas {W : Set ℂ} (hWo : IsOpen W)
    {g : ℂ → ℝ → ℂ}
    (hg : ContinuousOn (fun p : ℂ × ℝ => g p.1 p.2) (W ×ˢ Set.univ))
    (hhol : ∀ x : ℝ, DifferentiableOn ℂ (fun z => g z x) W)
    (hbound : ∀ z₀ ∈ W, ∃ r > 0, Metric.closedBall z₀ r ⊆ W ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ z ∈ Metric.closedBall z₀ (r / 2),
        ‖deriv (fun w => g w x) z‖ ≤ K)
    (hmeas : ∀ z₀ ∈ W, Measurable (fun x : ℝ => deriv (fun z => g z x) z₀)) :
    DifferentiableOn ℂ (fun z => ∫ x in (0 : ℝ)..1, g z x) W := by
  intro z₀ hz₀
  obtain ⟨r, hr, hsub, K, _hKnn, hboundK⟩ := hbound z₀ hz₀
  have hcont_g : ∀ x ∈ W, Continuous (fun t : ℝ => g x t) := fun x hx =>
    hg.comp_continuous (continuous_const.prodMk continuous_id) (fun t => by simp [hx])
  have hs : Metric.closedBall z₀ (r / 2) ∈ 𝓝 z₀ := Metric.closedBall_mem_nhds z₀ (by linarith)
  have h1 : ∀ᶠ x in 𝓝 z₀,
      AEStronglyMeasurable (fun t : ℝ => g x t) (volume.restrict (Set.uIoc 0 1)) := by
    filter_upwards [hWo.mem_nhds hz₀] with x hx
    exact (hcont_g x hx).aestronglyMeasurable
  have h2 : IntervalIntegrable (fun t : ℝ => g z₀ t) volume 0 1 :=
    (hcont_g z₀ hz₀).intervalIntegrable 0 1
  have h3 : AEStronglyMeasurable (fun t : ℝ => deriv (fun w => g w t) z₀)
      (volume.restrict (Set.uIoc 0 1)) :=
    (hmeas z₀ hz₀).aestronglyMeasurable
  have h4 : ∀ᵐ t ∂volume, t ∈ Set.uIoc (0 : ℝ) 1 →
      ∀ z ∈ Metric.closedBall z₀ (r / 2), ‖deriv (fun w => g w t) z‖ ≤ (fun _ : ℝ => K) t := by
    filter_upwards with t ht z hz
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    exact hboundK t ⟨ht.1.le, ht.2⟩ z hz
  have h5 : ∀ᵐ t ∂volume, t ∈ Set.uIoc (0 : ℝ) 1 →
      ∀ z ∈ Metric.closedBall z₀ (r / 2),
        HasDerivAt (fun z => g z t) (deriv (fun w => g w t) z) z := by
    filter_upwards with t _ht z hz
    exact ((hhol t).differentiableAt
      (hWo.mem_nhds (hsub (Metric.closedBall_subset_closedBall (by linarith) hz)))).hasDerivAt
  have key := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℂ) (μ := volume) (E := ℂ) (a := 0) (b := 1)
    (bound := fun _ : ℝ => K) (F := fun z x => g z x)
    (F' := fun z x => deriv (fun w => g w x) z)
    (x₀ := z₀) (s := Metric.closedBall z₀ (r / 2))
    hs h1 h2 h3 h4 intervalIntegrable_const h5).2
  exact key.differentiableAt.differentiableWithinAt

theorem fourierCoeff_holomorphic {W : Set ℂ} (hWo : IsOpen W) {f : ℂ → ℝ → ℂ}
    (hf : ContinuousOn (fun p : ℂ × ℝ => f p.1 p.2) (W ×ˢ univ))
    (hhol : ∀ x : ℝ, DifferentiableOn ℂ (fun z => f z x) W) (k : ℤ) :
    DifferentiableOn ℂ
      (fun z => ∫ x in (0 : ℝ)..1, f z x * Complex.exp (-(2 * Real.pi * Complex.I * (k : ℂ) * (x : ℂ)))) W := by
  have hcont : ContinuousOn
      (fun p : ℂ × ℝ => f p.1 p.2 * Complex.exp (-(2 * Real.pi * Complex.I * (k : ℂ) * (p.2 : ℂ))))
      (W ×ˢ univ) :=
    hf.mul (Complex.continuous_exp.comp_continuousOn (by fun_prop))
  have hslice : ∀ x : ℝ,
      DifferentiableOn ℂ (fun z => f z x * Complex.exp (-(2 * Real.pi * Complex.I * (k : ℂ) * (x : ℂ)))) W :=
    fun x => (hhol x).mul_const _
  exact integral_differentiableOn_of_bound_and_meas
    (g := fun z x => f z x * Complex.exp (-(2 * Real.pi * Complex.I * (k : ℂ) * (x : ℂ))))
    hWo hcont hslice
    (fun z₀ hz₀ => deriv_bound hWo hcont hslice hz₀)
    (fun z₀ hz₀ => measurable_deriv_param hWo hcont hslice hz₀)

end Work.TMComp.MAnalytic
