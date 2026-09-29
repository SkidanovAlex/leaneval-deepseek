import Mathlib
import Submission.Work.Holonomy3.comp_defs

namespace Work.Holonomy3

/-- An analytic function on the open ball of radius `ρ` around `0` is the sum of its Taylor
series at `0` throughout that ball; the series is packaged as a `PowerSeries ℂ` whose
constant term and linear coefficient are `ψ 0` and `deriv ψ 0` respectively. -/
theorem exists_taylor_series {ψ : ℂ → ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hψ : AnalyticOnNhd ℂ ψ (Metric.ball 0 ρ)) :
    ∃ Φ : PowerSeries ℂ, Φ.coeff 0 = ψ 0 ∧ Φ.coeff 1 = deriv ψ 0 ∧
      (∀ z : ℂ, ‖z‖ < ρ → HasSum (fun p : ℕ => Φ.coeff p * z ^ p) (ψ z)) := by
  refine ⟨PowerSeries.mk (fun n => ((n.factorial : ℕ) : ℂ)⁻¹ * iteratedDeriv n ψ 0), ?_, ?_, ?_⟩
  · simp [PowerSeries.coeff_mk, iteratedDeriv_zero]
  · simp [PowerSeries.coeff_mk, iteratedDeriv_one]
  · intro z hz
    have hdiff : DifferentiableOn ℂ ψ (Metric.ball (0 : ℂ) ρ) := hψ.differentiableOn
    have hmem : z ∈ Metric.ball (0 : ℂ) ρ := by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact hz
    have H := Complex.hasSum_taylorSeries_on_ball hdiff hmem
    simp only [sub_zero, smul_eq_mul] at H
    refine H.congr_fun (fun p => ?_)
    simp only [PowerSeries.coeff_mk]
    ring

end Work.Holonomy3
