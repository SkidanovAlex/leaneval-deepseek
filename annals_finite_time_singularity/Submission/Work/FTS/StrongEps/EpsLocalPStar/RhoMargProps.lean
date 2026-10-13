import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongEps.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology
open MeasureTheory Set Filter

/-- **The `t`-marginal of an admissible mollifier kernel.**  For `ρ` continuous, supported in the
closed unit ball of `ℝ²`, nonnegative with total mass `1` (the class
`Work.FTS.StrongEps.IsMollKernel`), the marginal `s ↦ ∫ t, ρ (s, t)` is continuous, nonnegative,
supported in `[-1, 1]`, and has total mass `1`.

This is the (one-dimensional) mollifier density that the trace-transfer identities
(`EpsLocalPStar/JepsTraceTransfer*.lean`) read off at the boundary of the quadrant, so that the
smooth, compactly supported one-dimensional kernel available in Mathlib's
`ContDiffBump`-vocabulary applies to the `z`-variable. -/
theorem RhoMargProps (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsMollKernel ρ) :
    Continuous (fun s : ℝ => ∫ t : ℝ, ρ (s, t)) ∧
    (∀ s : ℝ, 0 ≤ ∫ t : ℝ, ρ (s, t)) ∧
    (∀ s : ℝ, s ∉ Set.Icc (-1 : ℝ) 1 → (∫ t : ℝ, ρ (s, t)) = 0) ∧
    (∫ s : ℝ, (∫ t : ℝ, ρ (s, t))) = 1 := by
  classical
  -- `ρ (s, ·)` vanishes off the closed unit ball, *uniformly in* `s`: the support hypothesis
  -- gives `s² + t² ≤ 1` at every non-vanishing point, so `t` must lie in the ball.
  have hvanish : ∀ s t : ℝ, t ∉ Metric.closedBall (0 : ℝ) 1 → ρ (s, t) = 0 := by
    intro s t ht
    by_contra hne
    have hb : s ^ 2 + t ^ 2 ≤ 1 := by simpa using hρ.support (s, t) hne
    have ht2 : 1 < t ^ 2 := by
      have h1 : ¬ (dist t 0 ≤ 1) := by simpa [Metric.mem_closedBall] using ht
      rw [dist_eq_norm, sub_zero, Real.norm_eq_abs] at h1
      have h2 : 1 < |t| := not_le.mp h1
      nlinarith [abs_nonneg t, sq_abs t]
    nlinarith [sq_nonneg s]
  -- hence the marginal is the integral over the *compact* ball, for every `s`.
  have hident : ∀ s : ℝ, (∫ t : ℝ, ρ (s, t)) = ∫ t in Metric.closedBall (0 : ℝ) 1, ρ (s, t) := by
    intro s
    exact (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (f := fun t : ℝ => ρ (s, t)) (fun t ht => hvanish s t ht)).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- continuity: parametric integral of a continuous function over a compact set
    refine (continuous_parametric_integral_of_continuous (μ := volume)
      (f := fun s t : ℝ => ρ (s, t)) hρ.cont (isCompact_closedBall (0 : ℝ) 1)).congr ?_
    intro s
    exact (hident s).symm
  · -- nonnegativity
    intro s
    exact MeasureTheory.integral_nonneg (fun t => hρ.nonneg (s, t))
  · -- vanishing for `|s| > 1`
    intro s hs
    have hzero : ∀ t : ℝ, ρ (s, t) = 0 := by
      intro t
      by_contra hne
      have hb : s ^ 2 + t ^ 2 ≤ 1 := by simpa using hρ.support (s, t) hne
      have hs2 : 1 < s ^ 2 := by
        have h : s < -1 ∨ 1 < s := by
          rw [Set.mem_Icc, not_and_or] at hs
          rcases hs with h | h
          · exact Or.inl (not_le.mp h)
          · exact Or.inr (not_le.mp h)
        rcases h with h | h
        · nlinarith
        · nlinarith
      nlinarith [sq_nonneg t]
    simp [hzero]
  · -- total mass: Tonelli for the continuous, compactly supported `ρ`
    have hint : MeasureTheory.Integrable ρ (volume : Measure (ℝ × ℝ)) := by
      refine hρ.cont.integrable_of_hasCompactSupport ?_
      refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : ℝ × ℝ) 1) isClosed_closure
        (closure_minimal ?_ Metric.isClosed_closedBall)
      intro q hq
      rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
      have h1 : q.1 ^ 2 ≤ 1 ^ 2 := by
        have := hρ.support q hq
        nlinarith [sq_nonneg q.2]
      have h2 : q.2 ^ 2 ≤ 1 ^ 2 := by
        have := hρ.support q hq
        nlinarith [sq_nonneg q.1]
      refine max_le ?_ ?_
      · have := (sq_le_sq.mp h1 : |q.1| ≤ |(1 : ℝ)|)
        simpa using this
      · have := (sq_le_sq.mp h2 : |q.2| ≤ |(1 : ℝ)|)
        simpa using this
    have hint' : MeasureTheory.Integrable ρ (volume.prod volume : Measure (ℝ × ℝ)) := by
      rwa [← MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
    have h1 : (∫ p : ℝ × ℝ, ρ p ∂(volume.prod volume)) = ∫ s, ∫ t, ρ (s, t) :=
      MeasureTheory.integral_prod ρ hint'
    have h2 : (∫ p : ℝ × ℝ, ρ p ∂(volume.prod volume)) = 1 := by
      rw [← MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
      exact hρ.mass
    exact h1.symm.trans h2

end Work.FTS.StrongEps.EpsLocalPStar
