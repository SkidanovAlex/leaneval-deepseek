/-
# `Work.FTS.BSSwirl.potDeriv_eq_integral_potKerBall`

The candidate derivative

  `potDeriv ω x = (4π)⁻¹ • ∫ y, ‖x-y‖⁻³ • (⟪y-x, ·⟫ ⊗ ω y)`

of the vector Newtonian potential is an integral against the singular kernel `potKer` with the
singularity translated to `x`:

  `potDeriv ω x = (4π)⁻¹ • ∫ z, (potKer z).smulRight (ω (x + z))`.

If in addition `ω` is supported in the closed ball `B(0,R)`, then `ω (x + z) ≠ 0` forces
`‖z‖ ≤ R + ‖x‖`, so the kernel may be cut off to the ball `B(0,ρ)` whenever `R + ‖x‖ + 1 ≤ ρ`;
this is the *integrable* kernel `potKerBall ρ` (`Work.FTS.BSSwirl.CdAux`), and it is what makes
`potDeriv ω x` a genuine Bochner integral rather than a singular integral.

The proof is a combination of a change of variables (`z = y - x`, i.e. translation invariance of
the Lebesgue measure, `MeasureTheory.integral_sub_right_eq_self`) with the pointwise agreement of
`potKer` and `potKerBall ρ` on the support of `z ↦ ω (x+z)`
(`Work.FTS.BSSwirl.potKerBall_apply_of_mem`).  No regularity or integrability of `ω` is needed:
both sides are ordinary Bochner integrals of kernels, so the equality holds for *every* `ω`.
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.BSSwirl.Defs
import Submission.Work.FTS.BSSwirl.CdAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSSwirl

theorem potDeriv_eq_integral_potKerBall {ω : Work.FTS.BSSwirl.R3 → Work.FTS.BSSwirl.R3}
    {R ρ : ℝ} {x : Work.FTS.BSSwirl.R3}
    (hsupp : ∀ y, ω y ≠ 0 → y ∈ Metric.closedBall 0 R)
    (hρ : R + ‖x‖ + 1 ≤ ρ) :
    Work.FTS.BSSwirl.potDeriv ω x = (4 * Real.pi)⁻¹ •
      ∫ z, (Work.FTS.BSSwirl.potKerBall ρ z).smulRight (ω (x + z)) := by
  rw [Work.FTS.BSSwirl.potDeriv]
  congr 1
  -- Step 1: rewrite the integrand of `potDeriv` as `potKer (y-x)` applied to `ω y`, and change
  -- variables `z = y - x`.
  have h1 : (∫ y : R3, (‖x - y‖ ^ (3 : ℕ))⁻¹ • (innerSL ℝ (y - x)).smulRight (ω y))
      = ∫ z : R3, (potKer z).smulRight (ω (x + z)) := by
    have hcongr : ∀ y : R3,
        (‖x - y‖ ^ (3 : ℕ))⁻¹ • (innerSL ℝ (y - x)).smulRight (ω y)
          = (potKer (y - x)).smulRight (ω (x + (y - x))) := by
      intro y
      rw [show x + (y - x) = y by abel, norm_sub_rev, potKer_smulRight]
    have hcongr' : (∫ y : R3, (‖x - y‖ ^ (3 : ℕ))⁻¹ • (innerSL ℝ (y - x)).smulRight (ω y))
        = ∫ y : R3, (potKer (y - x)).smulRight (ω (x + (y - x))) :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hcongr)
    rw [hcongr']
    exact MeasureTheory.integral_sub_right_eq_self
      (fun z => (potKer z).smulRight (ω (x + z))) x
  -- Step 2: the cut-off kernel agrees with the singular one on the support of `z ↦ ω (x+z)`.
  have h2 : (∫ z : R3, (potKer z).smulRight (ω (x + z)))
      = ∫ z : R3, (potKerBall ρ z).smulRight (ω (x + z)) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with z
    by_cases hz : ω (x + z) = 0
    · simp only [hz, ContinuousLinearMap.smulRight_zero]
    · have hmem : x + z ∈ Metric.closedBall (0 : R3) R := hsupp (x + z) hz
      have hle : ‖x + z‖ ≤ R := by
        rw [Metric.mem_closedBall, dist_zero_right] at hmem
        exact hmem
      have hlt : ‖z‖ < ρ := by
        have hle' : ‖z‖ ≤ ‖x + z‖ + ‖x‖ := by
          have h := norm_sub_le (x + z) x
          rwa [show (x + z) - x = z by abel] at h
        linarith
      have hzball : z ∈ Metric.ball (0 : R3) ρ := by
        rw [Metric.mem_ball, dist_zero_right]
        exact hlt
      rw [potKerBall_apply_of_mem hzball]
  rw [h1]
  exact h2

end Work.FTS.BSSwirl
