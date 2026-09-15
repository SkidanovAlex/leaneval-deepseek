import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Separation.CompletelyRegular

open MeasureTheory Metric

namespace Commons.MeasureTheory.Integral

/-- For any `d`, there is a sequence `K n` of smooth, compactly supported, nonnegative
functions on `Fin d → ℂ` with `∫ K n = 1` and support contained in the closed ball of radius
`1 / (n + 1)` around `0`: an approximate identity (mollifier sequence).

This is built from `ContDiffBump.normed` applied to a bump whose outer radius is `1 / (n + 1)`. -/
theorem exists_approximate_identity_complex (d : ℕ) :
    ∃ K : ℕ → (Fin d → ℂ) → ℝ,
      (∀ (n : ℕ) (s : Fin d → ℂ), 0 ≤ K n s) ∧
      (∀ n : ℕ, ∫ s : Fin d → ℂ, K n s = 1) ∧
      (∀ n : ℕ, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (K n)) ∧
      (∀ n : ℕ, HasCompactSupport (K n)) ∧
      (∀ n : ℕ, Function.support (K n) ⊆ Metric.closedBall 0 (1 / (n + 1))) := by
  let bump : ℕ → ContDiffBump (0 : Fin d → ℂ) := fun n =>
    { rIn := (1 / (n + 1)) / 2
      rOut := 1 / (n + 1)
      rIn_pos := by positivity
      rIn_lt_rOut := by
        have h : (0 : ℝ) < 1 / (n + 1) := by positivity
        linarith }
  refine ⟨fun n => (bump n).normed volume, ?_, ?_, ?_, ?_, ?_⟩
  · intro n s
    exact (bump n).nonneg_normed s
  · intro n
    exact (bump n).integral_normed
  · intro n
    exact (bump n).contDiff_normed (n := ⊤)
  · intro n
    exact (bump n).hasCompactSupport_normed
  · intro n
    rw [(bump n).support_normed_eq]
    exact ball_subset_closedBall

end Commons.MeasureTheory.Integral