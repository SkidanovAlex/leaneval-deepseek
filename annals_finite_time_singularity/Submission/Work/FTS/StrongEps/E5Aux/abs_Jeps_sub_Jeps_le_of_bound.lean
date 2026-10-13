import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Jeps_tendsto_of_tendsto
import Submission.Work.FTS.StrongEps.Jker_integral_eq_one

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5Aux

/-- **`J_ε` of a difference is the integral of the kernel against the difference.**  On the open
quadrant the two mollified values may be written as the log-coordinate convolutions of `X` resp.
`Y` against `Jker ρ ε` (`Jeps_eq_integral`); the kernel has compact support and both shifted
profiles are continuous (the shift stays in the open quadrant, where `X` and `Y` are continuous),
so both products are integrable and `integral_sub` splits the difference. -/
theorem Jeps_sub_Jeps_eq_integral {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {X Y : ℝ → ℝ → ℝ} {ε z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) (hε : 0 < ε)
    (hXc : ContinuousOn (fun q : ℝ × ℝ => X q.1 q.2) Work.FTS.StrongEps.Quad)
    (hYc : ContinuousOn (fun q : ℝ × ℝ => Y q.1 q.2) Work.FTS.StrongEps.Quad) :
    Work.FTS.StrongEps.Jeps ρ ε X z θ - Work.FTS.StrongEps.Jeps ρ ε Y z θ
      = ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * (X (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)
            - Y (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) := by
  -- the shifted point stays in the open quadrant, whatever the shift `p`
  have hmem : ∀ p : ℝ × ℝ,
      (Work.FTS.StrongEps.zShift z p.1, Work.FTS.StrongEps.thShift θ p.2)
        ∈ Work.FTS.StrongEps.Quad :=
    fun _ => ⟨Work.FTS.StrongEps.zShift_pos hz, Work.FTS.StrongEps.thShift_mem hθ⟩
  -- hence the shifted profiles are continuous on all of `ℝ²`
  have hcontX : Continuous fun p : ℝ × ℝ =>
      X (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2) := by
    simpa only [Function.comp_def] using
      hXc.comp_continuous (Work.FTS.StrongEps.continuous_shift_pair z θ) hmem
  have hcontY : Continuous fun p : ℝ × ℝ =>
      Y (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2) := by
    simpa only [Function.comp_def] using
      hYc.comp_continuous (Work.FTS.StrongEps.continuous_shift_pair z θ) hmem
  -- the products with the (compactly supported) kernel are integrable
  have hXint : Integrable fun p : ℝ × ℝ =>
      Work.FTS.StrongEps.Jker ρ ε p
        * X (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2) :=
    ((Work.FTS.StrongEps.Jker_continuous hρ ε).mul hcontX).integrable_of_hasCompactSupport
      (Work.FTS.StrongEps.Jker_hasCompactSupport hρ hε).mul_right
  have hYint : Integrable fun p : ℝ × ℝ =>
      Work.FTS.StrongEps.Jker ρ ε p
        * Y (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2) :=
    ((Work.FTS.StrongEps.Jker_continuous hρ ε).mul hcontY).integrable_of_hasCompactSupport
      (Work.FTS.StrongEps.Jker_hasCompactSupport hρ hε).mul_right
  rw [Work.FTS.StrongEps.Jeps_eq_integral ρ ε X hz hθ,
    Work.FTS.StrongEps.Jeps_eq_integral ρ ε Y hz hθ, ← integral_sub hXint hYint]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  ring

theorem abs_Jeps_sub_Jeps_le_of_bound {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {X Y : ℝ → ℝ → ℝ} {ε z θ η : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) (hε : 0 < ε)
    (hXc : ContinuousOn (fun q : ℝ × ℝ => X q.1 q.2) Work.FTS.StrongEps.Quad)
    (hYc : ContinuousOn (fun q : ℝ × ℝ => Y q.1 q.2) Work.FTS.StrongEps.Quad)
    (hη : ∀ q : ℝ × ℝ, ‖q‖ ≤ ε →
      |X (Work.FTS.StrongEps.zShift z q.1) (Work.FTS.StrongEps.thShift θ q.2)
        - Y (Work.FTS.StrongEps.zShift z q.1) (Work.FTS.StrongEps.thShift θ q.2)| ≤ η) :
    |Work.FTS.StrongEps.Jeps ρ ε X z θ - Work.FTS.StrongEps.Jeps ρ ε Y z θ| ≤ η := by
  have hJnn : ∀ p : ℝ × ℝ, 0 ≤ Work.FTS.StrongEps.Jker ρ ε p := fun p => by
    simp only [Work.FTS.StrongEps.Jker]
    exact mul_nonneg (by positivity) (hρ.nonneg _)
  -- the difference is the integral of the kernel against the pointwise difference
  rw [Jeps_sub_Jeps_eq_integral hρ hz hθ hε hXc hYc]
  -- the pointwise difference is `≤ η` on the support of the kernel and the kernel vanishes off it
  have hpt : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)),
      ‖Work.FTS.StrongEps.Jker ρ ε p
        * (X (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)
          - Y (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2))‖
        ≤ Work.FTS.StrongEps.Jker ρ ε p * η := by
    refine Eventually.of_forall fun p => ?_
    by_cases hp : p ∈ Metric.closedBall (0 : ℝ × ℝ) ε
    · have hpe : ‖p‖ ≤ ε := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hp
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hJnn p)]
      exact mul_le_mul_of_nonneg_left (hη p hpe) (hJnn p)
    · rw [Work.FTS.StrongEps.Jker_eq_zero_of_not_mem hρ hε hp, zero_mul, norm_zero, zero_mul]
  -- the mass-one kernel turns the pointwise bound into the integral bound
  have hmain := norm_integral_le_of_norm_le
    ((Work.FTS.StrongEps.Jker_integrable hρ hε).mul_const η) hpt
  rw [integral_mul_const, Work.FTS.StrongEps.Jker_integral_eq_one ρ hρ hε, one_mul,
    Real.norm_eq_abs] at hmain
  exact hmain

end Work.FTS.StrongEps.E5Aux
