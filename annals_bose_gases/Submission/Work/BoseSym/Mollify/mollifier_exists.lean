import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Submission.Work.BoseSym.Interface
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# BoseSym — Mollify: existence of a mollifier sequence

For each `N` we construct a sequence `ρ n` of nonnegative smooth compactly
supported functions on the configuration space `Conf N = Fin N → E3`, each of
integral `1` (with respect to Lebesgue measure) and each supported in the ball
of radius `(n+1)⁻¹` about the origin.

The construction is the standard one: take Mathlib's bump function
`ContDiffBump (0 : Conf N)` with radii `R/4 < R/2` where `R = (n+1)⁻¹`, and
normalise it by its total mass using `ContDiffBump.normed`.  The normalised bump
is smooth, compactly supported, nonnegative, has integral `1` and has the closed
ball of radius `rOut = R/2` as its topological support, which lies strictly
inside the ball of radius `R`.
-/

namespace Work.BoseSym.Mollify

open MeasureTheory Filter
open scoped Topology Real ContDiff ENNReal NNReal Convolution

noncomputable section

set_option autoImplicit false

theorem mollifier_exists (N : ℕ) :
    ∃ ρ : ℕ → Conf N → ℝ,
      (∀ n, Smooth (ρ n)) ∧ (∀ n, HasCompactSupport (ρ n)) ∧ (∀ n, 0 ≤ ρ n) ∧
      (∀ n, intC N (ρ n) = 1) ∧ (∀ n, tsupport (ρ n) ⊆ Metric.ball 0 ((n : ℝ) + 1)⁻¹) := by
  have hR : ∀ n : ℕ, (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := fun n => by positivity
  -- the shrinking radii `rIn = R/4 < rOut = R/2 < R`
  let bump : ℕ → ContDiffBump (0 : Conf N) := fun n =>
    ⟨((n : ℝ) + 1)⁻¹ / 4, ((n : ℝ) + 1)⁻¹ / 2,
      by positivity,
      by have := hR n; linarith⟩
  refine ⟨fun n => (bump n).normed (volume : Measure (Conf N)), ?_, ?_, ?_, ?_, ?_⟩
  · intro n; exact (bump n).contDiff_normed
  · intro n; exact (bump n).hasCompactSupport_normed
  · intro n; exact (bump n).nonneg_normed
  · intro n; exact (bump n).integral_normed
  · -- the topological support is `closedBall 0 (R/2)`, contained in `ball 0 R`
    intro n
    rw [(bump n).tsupport_normed_eq]
    intro y hy
    rw [Metric.mem_closedBall] at hy
    rw [Metric.mem_ball]
    have h1 : ((n : ℝ) + 1)⁻¹ / 2 < ((n : ℝ) + 1)⁻¹ := by have := hR n; linarith
    exact lt_of_le_of_lt hy h1

end

end Work.BoseSym.Mollify
