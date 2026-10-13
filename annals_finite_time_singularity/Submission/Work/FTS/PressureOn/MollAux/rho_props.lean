import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Submission.Work.FTS.PressureOn.MollDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.MollAux

open MeasureTheory Filter
open scoped Topology

/-- The outer radius of `bump n` is `1 / (n + 1)`, by definition. -/
theorem bump_rOut (n : ℕ) :
    (Work.FTS.PressureOn.bump n).rOut = 1 / ((n : ℝ) + 1) := rfl

/-- The inner radius of `bump n` is `1 / (n + 2)`, by definition. -/
theorem bump_rIn (n : ℕ) :
    (Work.FTS.PressureOn.bump n).rIn = 1 / ((n : ℝ) + 2) := rfl

/-- `rho n` is the normalised bump `(bump n).normed volume`, by definition. -/
theorem rho_eq_normed (n : ℕ) :
    Work.FTS.PressureOn.rho n
      = (Work.FTS.PressureOn.bump n).normed MeasureTheory.volume := rfl

theorem rho_props (n : ℕ) :
    (∀ m : ℕ, ContDiff ℝ m (Work.FTS.PressureOn.rho n)) ∧
    HasCompactSupport (Work.FTS.PressureOn.rho n) ∧
    (∫ z, Work.FTS.PressureOn.rho n z) = 1 ∧
    (∀ z, 0 ≤ Work.FTS.PressureOn.rho n z) ∧
    (∀ z, Work.FTS.PressureOn.rho n (-z) = Work.FTS.PressureOn.rho n z) ∧
    (∀ z, Work.FTS.PressureOn.rho n z ≠ 0 → ‖z‖ ≤ 1 / ((n : ℝ) + 1)) ∧
    Filter.Tendsto (fun n : ℕ => (Work.FTS.PressureOn.bump n).rOut) Filter.atTop (nhds 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- smoothness
    intro m
    exact ContDiffBump.contDiff_normed (f := Work.FTS.PressureOn.bump n)
      (μ := MeasureTheory.volume)
  · -- compact support
    exact ContDiffBump.hasCompactSupport_normed (f := Work.FTS.PressureOn.bump n)
      (μ := MeasureTheory.volume)
  · -- normalisation
    exact ContDiffBump.integral_normed (f := Work.FTS.PressureOn.bump n)
      (μ := MeasureTheory.volume)
  · -- nonnegativity
    intro z
    exact ContDiffBump.nonneg_normed (f := Work.FTS.PressureOn.bump n)
      (μ := MeasureTheory.volume) z
  · -- symmetry
    intro z
    exact ContDiffBump.normed_neg (Work.FTS.PressureOn.bump n) z
  · -- support inside the ball of radius `rOut = 1/(n+1)`
    intro z hz
    have hmem : z ∈ Function.support
        ((Work.FTS.PressureOn.bump n).normed MeasureTheory.volume) := hz
    rw [ContDiffBump.support_normed_eq] at hmem
    rw [bump_rOut] at hmem
    rw [Metric.mem_ball, dist_zero_right] at hmem
    exact hmem.le
  · -- the outer radii tend to `0`
    simpa [Work.FTS.PressureOn.bump] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0))

end Work.FTS.PressureOn.MollAux
