import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.CircleIntegral

open Complex Metric Set Filter Function
open scoped Real Topology BigOperators

namespace Commons.Analysis.Complex

/-- The logarithmic derivative of a function analytic on a ball and zero-free on a
sphere is circle integrable (it is continuous on the sphere). -/
lemma circleIntegrable_logDeriv_of_analytic_ne {f : ℂ → ℂ} {R ρ : ℝ} (hρ : 0 ≤ ρ)
    (hρR : ρ < R) (hf : AnalyticOnNhd ℂ f (Metric.ball (0:ℂ) R))
    (hne : ∀ z ∈ Metric.sphere (0:ℂ) ρ, f z ≠ 0) :
    CircleIntegrable (fun z => logDeriv f z) 0 ρ := by
  apply ContinuousOn.circleIntegrable hρ
  have hsub : Metric.sphere (0:ℂ) ρ ⊆ Metric.ball (0:ℂ) R := Metric.sphere_subset_ball hρR
  have hcd : ContinuousOn (deriv f) (Metric.sphere (0:ℂ) ρ) :=
    (hf.deriv.continuousOn).mono hsub
  have hcf : ContinuousOn f (Metric.sphere (0:ℂ) ρ) :=
    hf.continuousOn.mono hsub
  have hquot : ContinuousOn (fun z => deriv f z / f z) (Metric.sphere (0:ℂ) ρ) :=
    hcd.div hcf hne
  simpa only [logDeriv_apply] using hquot

theorem circleIntegral_logDeriv_add_eq {R ρ : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.ball (0:ℂ) R)) (hg : AnalyticOnNhd ℂ g (Metric.ball (0:ℂ) R))
    (hfne : ∀ z ∈ Metric.sphere (0:ℂ) ρ, f z ≠ 0)
    (hlt : ∀ z ∈ Metric.sphere (0:ℂ) ρ, ‖g z‖ < ‖f z‖) :
    circleIntegral (fun z => logDeriv (fun w => f w + g w) z) 0 ρ =
      circleIntegral (fun z => logDeriv f z) 0 ρ := by
  let h : ℂ → ℂ := fun z => (f z + g z) / f z
  have hsub : Metric.sphere (0:ℂ) ρ ⊆ Metric.ball (0:ℂ) R := Metric.sphere_subset_ball hρR
  have hfg_ne : ∀ z ∈ Metric.sphere (0:ℂ) ρ, f z + g z ≠ 0 := by
    intro z hz h0
    have hle : ‖f z‖ ≤ ‖g z‖ := by
      have hsplit : f z = (f z + g z) - g z := by ring
      calc ‖f z‖ = ‖(f z + g z) - g z‖ := by rw [← hsplit]
        _ ≤ ‖f z + g z‖ + ‖g z‖ := norm_sub_le _ _
        _ = ‖g z‖ := by rw [h0]; simp
    linarith [hlt z hz]
  have hlogDeriv : ∀ z ∈ Metric.sphere (0:ℂ) ρ,
      logDeriv h z = logDeriv (fun w => f w + g w) z - logDeriv f z := by
    intro z hz
    have hzR : z ∈ Metric.ball (0:ℂ) R := hsub hz
    have hfz : AnalyticAt ℂ f z := hf z hzR
    have hgz : AnalyticAt ℂ g z := hg z hzR
    have hfz_ne : f z ≠ 0 := hfne z hz
    exact logDeriv_div (f := fun w => f w + g w) (g := f) z (hfg_ne z hz) hfz_ne
      (hfz.differentiableAt.add hgz.differentiableAt) hfz.differentiableAt
  have hzero : circleIntegral (fun z => logDeriv h z) 0 ρ = 0 := by
    refine circleIntegral.integral_eq_zero_of_hasDerivWithinAt' (f := Complex.log ∘ h) ?_
    intro z hz
    rw [abs_of_pos hρ] at hz ⊢
    have hzR : z ∈ Metric.ball (0:ℂ) R := hsub hz
    have hfz : AnalyticAt ℂ f z := hf z hzR
    have hgz : AnalyticAt ℂ g z := hg z hzR
    have hfz_ne : f z ≠ 0 := hfne z hz
    have hg_lt : ‖g z‖ < ‖f z‖ := hlt z hz
    have hfg_diff : DifferentiableAt ℂ (fun w => f w + g w) z :=
      hfz.differentiableAt.add hgz.differentiableAt
    have hdiff : DifferentiableAt ℂ h z := by
      have h1 : DifferentiableAt ℂ (fun w => (f w + g w) / f w) z :=
        hfg_diff.div hfz.differentiableAt hfz_ne
      simpa only [h] using h1
    have hmem : h z ∈ slitPlane := by
      apply ball_one_subset_slitPlane
      simp only [Metric.mem_ball, dist_eq_norm]
      have hH1 : h z - 1 = g z / f z := by
        simp only [h]
        rw [← div_self hfz_ne, ← sub_div]
        ring
      rw [hH1, norm_div, div_lt_one (norm_pos_iff.mpr hfz_ne)]
      exact hg_lt
    have hdh : HasDerivAt h (deriv h z) z := hdiff.hasDerivAt
    exact (hdh.clog hmem).hasDerivWithinAt
  have hInt1 : CircleIntegrable (fun z => logDeriv (fun w => f w + g w) z) 0 ρ :=
    circleIntegrable_logDeriv_of_analytic_ne hρ.le hρR (hf.add hg) hfg_ne
  have hInt2 : CircleIntegrable (fun z => logDeriv f z) 0 ρ :=
    circleIntegrable_logDeriv_of_analytic_ne hρ.le hρR hf hfne
  have hcongr : circleIntegral (fun z => logDeriv h z) 0 ρ =
      circleIntegral (fun z => logDeriv (fun w => f w + g w) z - logDeriv f z) 0 ρ :=
    circleIntegral.integral_congr hρ.le (fun z hz => hlogDeriv z hz)
  have hsubst : circleIntegral (fun z => logDeriv (fun w => f w + g w) z - logDeriv f z) 0 ρ =
      circleIntegral (fun z => logDeriv (fun w => f w + g w) z) 0 ρ -
        circleIntegral (fun z => logDeriv f z) 0 ρ :=
    circleIntegral.integral_sub hInt1 hInt2
  have hfin : circleIntegral (fun z => logDeriv (fun w => f w + g w) z) 0 ρ -
      circleIntegral (fun z => logDeriv f z) 0 ρ = 0 := by
    rw [← hsubst, ← hcongr, hzero]
  exact sub_eq_zero.mp hfin

end Commons.Analysis.Complex