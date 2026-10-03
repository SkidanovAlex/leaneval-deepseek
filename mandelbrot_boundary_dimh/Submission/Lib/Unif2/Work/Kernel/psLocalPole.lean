import Mathlib
import Submission.Lib.Unif2.Work.Drive.chartPoleIdentity
import Submission.Lib.Unif2.Work.Drive.chartPoleIdentity_nhds
import Submission.Lib.Unif2.Work.Drive.pairTerm_clamping_reduce

/-!
# Working copies of the chart-local pole term

`Submission/Work/Kernel/pairTerm_pole_general.lean` (and the file it imports,
`pairTerm_pole_centered.lean`) do not compile at the moment, for a reason unrelated to their content:
both import `Submission.Work.Kernel.pairing_harmonic_zero_kernel`, which a refactor broke.  This
module carries the two lemmas needed by the pole identity, with every declaration renamed by the
prefix `ps`, so that the pole identity can be reproved independently of those files.

* `Work.Kernel.psPairTerm_zero_weight` — a pairing term with the zero weight vanishes.
* `Work.Kernel.psPairTerm_pole_of_logExpansion` — the chart-local pole identity with an arbitrary
  pole chart (the form needed when the pole chart is not centred at the pole).
-/

open MeasureTheory Set Filter
open scoped Manifold Topology Gradient

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.Kernel

/-- A pairing term with the zero weight vanishes. -/
theorem psPairTerm_zero_weight {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    (x : X) (ρ σ : ℝ) (f χ : X → ℝ) :
    Work.Drive.pairTerm x ρ σ (fun _ => (0 : ℝ)) f χ = 0 := by
  have h0 : (fun _ : X => (0 : ℝ)) = (0 : X → ℝ) := rfl
  rw [Work.Drive.pairTerm, h0, Work.Drive.clampedPullback_zero]
  simp


/-- **The chart-local pole term, for an arbitrary chart.** -/
theorem psPairTerm_pole_of_logExpansion {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {x₀ : X} {f χ : X → ℝ} {H : ℂ → ℝ} {p : ℂ} {ρ r σ : ℝ}
    (hσ : 0 ≤ σ) (hσρ : σ < ρ) (hrρ : r ≤ ρ)
    (htgt : Metric.ball ((chartAt ℂ x₀) x₀) ρ ⊆ (chartAt ℂ x₀).target)
    (hχsupp : tsupport χ ⊆ (chartAt ℂ x₀) ⁻¹' Metric.ball ((chartAt ℂ x₀) x₀) σ)
    (hH : InnerProductSpace.HarmonicOnNhd H (Metric.ball p r))
    (hueq : ∀ z ∈ Metric.ball p r,
      f ((chartAt ℂ x₀).symm z) = -Real.log ‖z - p‖ + H z)
    (hχc1 : ContDiff ℝ 1 (Work.Drive.clampedPullback x₀ ρ χ))
    (hχcs : HasCompactSupport (Work.Drive.clampedPullback x₀ ρ χ))
    (hχball : tsupport (Work.Drive.clampedPullback x₀ ρ χ) ⊆ Metric.ball p r)
    (hi1 : Integrable (fun z : ℂ =>
      inner (𝕜 := ℝ) (gradient (fun y : ℂ => -Real.log ‖y - p‖) z)
        (gradient (Work.Drive.clampedPullback x₀ ρ χ) z)))
    (hi2 : Integrable (fun z : ℂ =>
      inner (𝕜 := ℝ) (gradient H z) (gradient (Work.Drive.clampedPullback x₀ ρ χ) z)))
    (hint : Integrable (fun z : ℂ =>
      inner (𝕜 := ℝ) (gradient (Work.Drive.clampedPullback x₀ ρ f) z)
        (gradient (Work.Drive.clampedPullback x₀ ρ χ) z))) :
    Work.Drive.pairTerm x₀ ρ σ (fun _ : X => (1 : ℝ)) f χ
      = 2 * Real.pi * Work.Drive.clampedPullback x₀ ρ χ p := by
  classical
  -- The support of the clamped test function lies in the closed ball of radius `σ`.
  have hsuppσ : tsupport (Work.Drive.clampedPullback x₀ ρ χ) ⊆
      Metric.closedBall ((chartAt ℂ x₀) x₀) σ := by
    refine closure_minimal ?_ Metric.isClosed_closedBall
    intro z hz
    rw [Function.mem_support] at hz
    have hzρ : z ∈ Metric.ball ((chartAt ℂ x₀) x₀) ρ := by
      by_contra hcon
      exact hz (Work.Drive.clampedPullback_eq_zero_of_notMem_ball (u := χ) hcon)
    rw [Metric.mem_closedBall]
    have hχne : χ ((chartAt ℂ x₀).symm z) ≠ 0 := by
      rw [← Work.Drive.clampedPullback_apply_of_mem (u := χ) hzρ]
      exact hz
    have hy : (chartAt ℂ x₀).symm z ∈ tsupport χ :=
      subset_tsupport _ (Function.mem_support.mpr hχne)
    have hball := hχsupp hy
    rw [Set.mem_preimage, (chartAt ℂ x₀).right_inv (htgt hzρ)] at hball
    exact le_of_lt hball
  -- The clamped weight `1` may be dropped from the integrand, a.e.
  have hae : (fun z : ℂ => Work.Drive.clampedPullback x₀ σ (fun _ : X => (1 : ℝ)) z *
        inner (𝕜 := ℝ) (gradient (Work.Drive.clampedPullback x₀ ρ f) z)
          (gradient (Work.Drive.clampedPullback x₀ ρ χ) z))
      =ᵐ[volume] fun z : ℂ =>
        inner (𝕜 := ℝ) (gradient (Work.Drive.clampedPullback x₀ ρ f) z)
          (gradient (Work.Drive.clampedPullback x₀ ρ χ) z) := by
    filter_upwards [compl_mem_ae_iff.mpr (MeasureTheory.Measure.addHaar_sphere volume
      ((chartAt ℂ x₀) x₀) σ)] with z hz
    have hzne : dist z ((chartAt ℂ x₀) x₀) ≠ σ := fun hcon =>
      hz (by rw [Metric.mem_sphere]; exact hcon)
    rcases lt_or_gt_of_ne hzne with hlt | hgt
    · rw [Work.Drive.clampedPullback_apply_of_mem (u := fun _ : X => (1 : ℝ))
        (Metric.mem_ball.mpr hlt), one_mul]
    · have hw : Work.Drive.clampedPullback x₀ σ (fun _ : X => (1 : ℝ)) z = 0 :=
        Work.Drive.clampedPullback_eq_zero_of_notMem_ball (u := fun _ : X => (1 : ℝ))
          (fun hcon => absurd (Metric.mem_ball.mp hcon) (not_lt.mpr (le_of_lt hgt)))
      have hnot : z ∉ tsupport (Work.Drive.clampedPullback x₀ ρ χ) := fun hcon =>
        (not_le.mpr hgt) (Metric.mem_closedBall.mp (hsuppσ hcon))
      rw [hw, zero_mul,
        Work.Analysis.Harmonic.gradient_eq_zero_of_notMem_tsupport hnot, inner_zero_right]
  -- The local hypothesis of the chart-local pole identity.
  have hloc : ∀ z ∈ tsupport (Work.Drive.clampedPullback x₀ ρ χ),
      Work.Drive.clampedPullback x₀ ρ f
        =ᶠ[𝓝 z] fun w => -Real.log ‖w - p‖ + H w := by
    intro z hz
    have hzρ : z ∈ Metric.ball ((chartAt ℂ x₀) x₀) ρ := by
      rw [Metric.mem_ball]
      exact lt_of_le_of_lt (Metric.mem_closedBall.mp (hsuppσ hz)) hσρ
    have hzr : z ∈ Metric.ball p r := hχball hz
    have hopen : Metric.ball p r ∩ Metric.ball ((chartAt ℂ x₀) x₀) ρ ∈ 𝓝 z :=
      Filter.inter_mem (Metric.isOpen_ball.mem_nhds hzr) (Metric.isOpen_ball.mem_nhds hzρ)
    filter_upwards [hopen] with w hw
    rw [Work.Drive.clampedPullback_apply_of_mem (u := f) hw.2, hueq w hw.1]
  rw [Work.Drive.pairTerm, integral_congr_ae hae]
  exact Work.Drive.integral_inner_gradient_of_logExpansion_of_nhds (u := Work.Drive.clampedPullback x₀ ρ f)
    hH hχc1 hχcs hχball hloc hi1 hi2


end Work.Kernel
