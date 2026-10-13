import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.SolutionDelivery.Defs
import Submission.Work.StabilityFar.Deriv.hasFDerivAt_uncurry_apply

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The time block of the core `C^{1,α}` regularity of `ω`

`Work.StabilityFar.TimeHolderOnBall α ω R T H` is the *time*-`α`-Hölder regularity of the
vorticity `ω` on the support ball `B(0,R)`, over the two-sided window `[-1,T+1]`:

  `‖ω z t - ω z τ‖ ≤ H |t-τ|^α`   for `z ∈ B(0,R)`, `t, τ ∈ window T`.

`St4` (the far-field estimate) consumes this for the *vorticity itself* **and** for its time
derivative `∂ₜω = timeDeriv ω`.  This file delivers the second one from the core `C^{1,α}`
regularity of `ω.uncurry`, on the slightly larger ball `B(0,ρ)` with `R < ρ`: the time block of
the joint derivative `D(ω.uncurry)` *is* `∂ₜω` (`Work.StabilityFar.Deriv.hasFDerivAt_uncurry_apply`),
and the `α`-Hölder bound on `D(ω.uncurry)` on the core strip is exactly the hypothesis `hcore`.

The strict inequality `R < ρ` is what makes the boundary of the support ball `B(0,R)` an
*interior* point of the core region `B(0,ρ)`; there `fderivWithin` agrees with `fderiv` and the
uncurried field is genuinely differentiable, so the block identity applies.
-/

namespace Work.SolutionDelivery.Holder

open Set Metric FiniteTimeSingularity
open scoped Topology NNReal

/-- The `t`-block of the joint derivative `D(ω.uncurry)(z,t)` is the time derivative `∂ₜω z t`. -/
theorem timeDeriv_eq_fderiv_uncurry_mk {ω : Work.SolutionDelivery.R3 → ℝ → Work.SolutionDelivery.R3}
    {z : Work.SolutionDelivery.R3} {t : ℝ}
    (hf : HasFDerivAt ω.uncurry (fderiv ℝ ω.uncurry (z, t)) (z, t)) :
    timeDeriv ω z t
      = fderiv ℝ ω.uncurry (z, t) ((0 : Work.SolutionDelivery.R3), (1 : ℝ)) := by
  rw [Work.StabilityFar.Deriv.hasFDerivAt_uncurry_apply hf (0 : Work.SolutionDelivery.R3) (1 : ℝ)]
  simp

/-- **The time derivative of the core vorticity is time-`α`-Hölder on the support ball.**

If `ω.uncurry` is of class `C^{1,α}` on the core strip `B(0,ρ) × (-2, T+2)` with `R < ρ`, then
`∂ₜω` is `α`-Hölder in time on `B(0,R)` over the window `[-1,T+1]`, with a constant that is
simply the Hölder constant of `D(ω.uncurry)`. -/
theorem timeHolderOnBall_timeDeriv_of_isContDiffHolderOn {α : NNReal}
    {ω : Work.SolutionDelivery.R3 → ℝ → Work.SolutionDelivery.R3} {ρ R T : ℝ}
    (hρ : R < ρ)
    (hcore : IsContDiffHolderOn ℝ α ω.uncurry
      (Work.StabilityFar.coreRegion ρ ×ˢ Work.SolutionDelivery.extWindow T)) :
    ∃ H₁ : ℝ, 0 ≤ H₁ ∧
      Work.StabilityFar.TimeHolderOnBall (α : ℝ) (FiniteTimeSingularity.timeDeriv ω) R T H₁ := by
  obtain ⟨hcd, -, hholder⟩ := hcore
  obtain ⟨C, hC⟩ := hholder
  refine ⟨(C : ℝ), C.coe_nonneg, ?_⟩
  intro z hz t ht τ hτ
  -- `z` is strictly inside the core ball: `R < ρ` and `‖z‖ ≤ R`.
  have hzR : ‖z‖ ≤ R := by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hz
    exact hz
  have hzlt : ‖z‖ < ρ := lt_of_le_of_lt hzR hρ
  -- both times lie in the extended window.
  have ht_ext : t ∈ Work.SolutionDelivery.extWindow T :=
    Work.SolutionDelivery.window_subset_extWindow T ht
  have hτ_ext : τ ∈ Work.SolutionDelivery.extWindow T :=
    Work.SolutionDelivery.window_subset_extWindow T hτ
  -- the core strip contains an open neighbourhood of `(z,t)` and of `(z,τ)`.
  have hsub : Metric.ball (0 : Work.SolutionDelivery.R3) ρ ×ˢ Work.SolutionDelivery.extWindow T ⊆
      Work.StabilityFar.coreRegion ρ ×ˢ Work.SolutionDelivery.extWindow T := by
    rintro ⟨x, s⟩ hp
    simp only [Set.mem_prod, Metric.mem_ball, dist_eq_norm, sub_zero,
      Work.StabilityFar.mem_coreRegion] at hp ⊢
    exact ⟨hp.1.le, hp.2⟩
  have hmemt : (z, t) ∈ Metric.ball (0 : Work.SolutionDelivery.R3) ρ ×ˢ
      Work.SolutionDelivery.extWindow T := by
    rw [Set.mem_prod, Metric.mem_ball, dist_eq_norm, sub_zero]
    exact ⟨hzlt, ht_ext⟩
  have hmemτ : (z, τ) ∈ Metric.ball (0 : Work.SolutionDelivery.R3) ρ ×ˢ
      Work.SolutionDelivery.extWindow T := by
    rw [Set.mem_prod, Metric.mem_ball, dist_eq_norm, sub_zero]
    exact ⟨hzlt, hτ_ext⟩
  have hnhds_t : Work.StabilityFar.coreRegion ρ ×ˢ Work.SolutionDelivery.extWindow T ∈ 𝓝 (z, t) :=
    Filter.mem_of_superset
      ((isOpen_ball.prod (Work.SolutionDelivery.isOpen_extWindow T)).mem_nhds hmemt) hsub
  have hnhds_τ : Work.StabilityFar.coreRegion ρ ×ˢ Work.SolutionDelivery.extWindow T ∈ 𝓝 (z, τ) :=
    Filter.mem_of_superset
      ((isOpen_ball.prod (Work.SolutionDelivery.isOpen_extWindow T)).mem_nhds hmemτ) hsub
  have hst : (z, t) ∈ Work.StabilityFar.coreRegion ρ ×ˢ Work.SolutionDelivery.extWindow T :=
    hsub hmemt
  have hsτ : (z, τ) ∈ Work.StabilityFar.coreRegion ρ ×ˢ Work.SolutionDelivery.extWindow T :=
    hsub hmemτ
  -- differentiability of the uncurried field at the two points.
  have hft : HasFDerivAt ω.uncurry (fderiv ℝ ω.uncurry (z, t)) (z, t) :=
    ((hcd.contDiffAt hnhds_t).differentiableAt (by norm_num)).hasFDerivAt
  have hfτ : HasFDerivAt ω.uncurry (fderiv ℝ ω.uncurry (z, τ)) (z, τ) :=
    ((hcd.contDiffAt hnhds_τ).differentiableAt (by norm_num)).hasFDerivAt
  -- the time derivative is the `t`-block of the joint derivative.
  have hkeyt := timeDeriv_eq_fderiv_uncurry_mk hft
  have hkeyτ := timeDeriv_eq_fderiv_uncurry_mk hfτ
  -- and at an interior point, `fderivWithin` of the core strip is the honest derivative.
  have hfw_t : fderivWithin ℝ ω.uncurry
      (Work.StabilityFar.coreRegion ρ ×ˢ Work.SolutionDelivery.extWindow T) (z, t)
      = fderiv ℝ ω.uncurry (z, t) := fderivWithin_of_mem_nhds hnhds_t
  have hfw_τ : fderivWithin ℝ ω.uncurry
      (Work.StabilityFar.coreRegion ρ ×ˢ Work.SolutionDelivery.extWindow T) (z, τ)
      = fderiv ℝ ω.uncurry (z, τ) := fderivWithin_of_mem_nhds hnhds_τ
  have hdist : dist (z, t) (z, τ) = |t - τ| := by
    rw [Prod.dist_eq, dist_self, Real.dist_eq, max_eq_right (abs_nonneg _)]
  have hhold := norm_le_of_holderOnWith hC (z, t) hst (z, τ) hsτ
  have hone : ‖((0 : Work.SolutionDelivery.R3), (1 : ℝ))‖ = 1 := by
    rw [Prod.norm_def, norm_zero, norm_one, max_eq_right zero_le_one]
  calc ‖timeDeriv ω z t - timeDeriv ω z τ‖
      = ‖(fderiv ℝ ω.uncurry (z, t) - fderiv ℝ ω.uncurry (z, τ))
          ((0 : Work.SolutionDelivery.R3), (1 : ℝ))‖ := by
        rw [hkeyt, hkeyτ, sub_apply]
    _ ≤ ‖fderiv ℝ ω.uncurry (z, t) - fderiv ℝ ω.uncurry (z, τ)‖ *
          ‖((0 : Work.SolutionDelivery.R3), (1 : ℝ))‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖fderiv ℝ ω.uncurry (z, t) - fderiv ℝ ω.uncurry (z, τ)‖ := by rw [hone, mul_one]
    _ = ‖fderivWithin ℝ ω.uncurry
            (Work.StabilityFar.coreRegion ρ ×ˢ Work.SolutionDelivery.extWindow T) (z, t)
          - fderivWithin ℝ ω.uncurry
            (Work.StabilityFar.coreRegion ρ ×ˢ Work.SolutionDelivery.extWindow T) (z, τ)‖ := by
        rw [hfw_t, hfw_τ]
    _ ≤ (C : ℝ) * dist (z, t) (z, τ) ^ (α : ℝ) := hhold
    _ = (C : ℝ) * |t - τ| ^ (α : ℝ) := by rw [hdist]

end Work.SolutionDelivery.Holder

