import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.PressureOn.PoissonAux.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Metric Filter
open scoped Topology

namespace Work.FTS.PressureOn.PoissonAux

/-!
# A uniform bound for the derivative of the profile `radialCut`

The profile `χ = radialCut` is `C^∞`, equals `1` on `(-∞,1]` and `0` on `[2,∞)`.  Hence its
derivative is continuous and supported in the compact interval `[1,2]`: it is zero on the open
set where `χ` is locally the constant `1` (below `1`) or the constant `0` (above `2`).
Continuity plus compact support then gives a uniform bound.
-/

/-- For `t < 1` the profile `radialCut` is locally the constant `1`. -/
theorem eventuallyEq_one_of_lt_one {t : ℝ} (ht : t < 1) :
    radialCut =ᶠ[𝓝 t] fun _ : ℝ => (1 : ℝ) := by
  filter_upwards [isOpen_Iio.mem_nhds ht] with s hs
  exact radialCut_eq_one (le_of_lt hs)

/-- For `2 < t` the profile `radialCut` is locally the constant `0`. -/
theorem eventuallyEq_zero_of_lt {t : ℝ} (ht : 2 < t) :
    radialCut =ᶠ[𝓝 t] fun _ : ℝ => (0 : ℝ) := by
  filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
  exact radialCut_eq_zero (le_of_lt hs)

/-- The derivative of `radialCut` is supported in the ball of radius `2` about `0`. -/
theorem support_deriv_radialCut_subset :
    Function.support (deriv radialCut) ⊆ closedBall (0 : ℝ) 2 := by
  intro t ht
  rw [mem_closedBall, dist_eq_norm, sub_zero, Real.norm_eq_abs]
  by_contra h
  rw [not_le] at h
  have hz : deriv radialCut t = 0 := by
    rcases lt_abs.mp h with h2 | h2
    · rw [(eventuallyEq_zero_of_lt h2).deriv_eq]; simp
    · rw [(eventuallyEq_one_of_lt_one (by linarith)).deriv_eq]; simp
  exact (Function.mem_support.mp ht) hz

/-- The derivative of `radialCut` has compact support. -/
theorem hasCompactSupport_deriv_radialCut : HasCompactSupport (deriv radialCut) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℝ) 2)
    support_deriv_radialCut_subset

/-- The derivative of `radialCut` is continuous. -/
theorem continuous_deriv_radialCut : Continuous (deriv radialCut) :=
  (contDiff_radialCut 1).continuous_deriv_one

/-- The derivative of the cutoff profile `radialCut` (defined in
`Submission/Work/FTS/PressureOn/PoissonAux/Defs.lean` as
`Work.FTS.PressureOn.radialCut t = Real.smoothTransition (2 - t)`, so that it is `1` on
`(-∞,1]` and `0` on `[2,∞)`) is bounded on all of `ℝ`. -/
theorem exists_bound_deriv_radialCut :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, |deriv Work.FTS.PressureOn.radialCut t| ≤ B := by
  obtain ⟨C, hC⟩ := continuous_deriv_radialCut.bounded_above_of_compact_support
    hasCompactSupport_deriv_radialCut
  exact ⟨C, le_trans (norm_nonneg _) (hC 0), fun t => by
    simpa only [Real.norm_eq_abs] using hC t⟩

end Work.FTS.PressureOn.PoissonAux
