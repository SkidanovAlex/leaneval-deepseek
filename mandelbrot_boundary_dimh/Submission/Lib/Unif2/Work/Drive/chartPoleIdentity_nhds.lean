import Mathlib
import Submission.Lib.Unif2.Work.Drive.chartPoleIdentity

/-!
# The chart-local pole identity with *local* hypotheses

`Work.Drive.integral_inner_gradient_of_logExpansion` requires the logarithmic expansion
`u = -log ‖· - p‖ + H` on the **whole** ball `ball p ρ`.  For the Dirichlet pairing this is too much:
the clamped chart pullback that plays the role of `u` is clamped against the ball centred at the
*chart's* centre, whereas the pole `p` is the image of another point, so the expansion is only
available along a neighbourhood of the **support of the test function**.

This file proves the same identity under the local hypothesis

  `∀ z ∈ tsupport Φ, u =ᶠ[𝓝 z] (fun w => -log ‖w - p‖ + H w)`,

i.e. the two functions agree on a neighbourhood of every point of the support of `Φ`.  The proof is a
one-line modification of the original (the `hueq` is used exactly there), and nothing else changes.
-/

open MeasureTheory Set Filter
open scoped Manifold Topology Gradient

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.Drive

/-- **The chart-local pole identity, with the expansion required only near the support of `Φ`.** -/
theorem integral_inner_gradient_of_logExpansion_of_nhds {u H : ℂ → ℝ} {p : ℂ} {ρ : ℝ}
    (hH : InnerProductSpace.HarmonicOnNhd H (Metric.ball p ρ))
    {Φ : ℂ → ℝ} (hΦ : ContDiff ℝ 1 Φ) (hΦc : HasCompactSupport Φ)
    (hΦsupp : tsupport Φ ⊆ Metric.ball p ρ)
    (hueq : ∀ z ∈ tsupport Φ, u =ᶠ[𝓝 z] fun w => -Real.log ‖w - p‖ + H w)
    (hi1 : Integrable (fun z : ℂ =>
      inner (𝕜 := ℝ) (gradient (fun y : ℂ => -Real.log ‖y - p‖) z) (gradient Φ z)))
    (hi2 : Integrable (fun z : ℂ =>
      inner (𝕜 := ℝ) (gradient H z) (gradient Φ z))) :
    ∫ z : ℂ, inner (𝕜 := ℝ) (gradient u z) (gradient Φ z) = 2 * Real.pi * Φ p := by
  have hae : ∀ᵐ z ∂(volume : Measure ℂ), inner (𝕜 := ℝ) (gradient u z) (gradient Φ z)
      = inner (𝕜 := ℝ) (gradient (fun y : ℂ => -Real.log ‖y - p‖) z) (gradient Φ z)
        + inner (𝕜 := ℝ) (gradient H z) (gradient Φ z) := by
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton p)] with z hzp
    by_cases hzs : z ∈ tsupport Φ
    · by_cases hz : z ∈ Metric.ball p ρ
      · have hev : u =ᶠ[𝓝 z] fun w => -Real.log ‖w - p‖ + H w := hueq z hzs
        have hdiff : DifferentiableAt ℝ (fun w : ℂ => -Real.log ‖w - p‖) z :=
          (Work.Drive.hasFDerivAt_neg_log_norm_sub hzp).differentiableAt
        have hHdiff : DifferentiableAt ℝ H z := (hH z hz).1.differentiableAt (by norm_num)
        have h1 : gradient u z
            = gradient (fun w : ℂ => -Real.log ‖w - p‖) z + gradient H z := by
          rw [Filter.EventuallyEq.gradient_eq hev]
          exact gradient_add_of_differentiableAt hdiff hHdiff
        rw [h1, inner_add_left]
      · exact absurd (hΦsupp hzs) hz
    · have hΦz : gradient Φ z = 0 :=
        Work.Analysis.Harmonic.gradient_eq_zero_of_notMem_tsupport hzs
      simp [hΦz]
  rw [integral_congr_ae hae, integral_add hi1 hi2,
    Work.Drive.integral_inner_gradient_logNorm_eq hΦ hΦc]
  have hzero : (∫ z : ℂ, inner (𝕜 := ℝ) (gradient H z) (gradient Φ z)) = 0 :=
    Work.Analysis.Harmonic.integral_inner_gradient_eq_zero
      (fun z hz => hH z (hΦsupp hz)) hΦ hΦc
  rw [hzero, add_zero]

end Work.Drive
