/-
# `Work.LWP.BiotSavart.farField_decay_const` — far-field decay with the sharp constant

For a vorticity `ω` bounded by `M ≥ 0` and supported in the closed ball of radius `R ≥ 0`
about the origin, the Newtonian-potential Biot–Savart field decays like `‖x‖⁻²` at infinity,
with the *explicit* constant `4/3`:

  `‖biotSavart ω x‖ ≤ (4/3) · M · R³ / ‖x‖²`   whenever `2R ≤ ‖x‖`.

This is the constant-explicit form of `Work.LWP.BiotSavart.farField_decay` (which only asserts
the existence of *some* positive constant), and it is the shape the LWP/BKM assembly consumes.

The proof is the elementary estimate on the Biot–Savart kernel
`K(x,y) = (4π)⁻¹ ω(y) × (x-y)/‖x-y‖³`: for `‖y‖ ≤ R` and `2R ≤ ‖x‖` one has
`‖x - y‖ ≥ ‖x‖/2`, hence

  `‖K(x,y)‖ ≤ (4π)⁻¹ · ‖ω y‖ · 4/‖x‖² ≤ (4π)⁻¹ · (4M/‖x‖²)`,

and the integrand vanishes off the ball, whose volume is `(4π/3) R³`:

  `‖biotSavart ω x‖ ≤ (4π)⁻¹ · (4M/‖x‖²) · (4πR³/3) = (4/3) M R³/‖x‖²`.

The two analytic ingredients are companion files of this directory:
`Work.LWP.BiotSavart.integrand_norm_le` (the pointwise kernel bound) and
`Work.LWP.BiotSavart.volume_closedBall_real` (the volume of the ball).
-/
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Submission.Work.LWP.Defs
import Submission.Work.LWP.BiotSavart.volume_closedBall_real
import Submission.Work.LWP.BiotSavart.integrand_norm_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity MeasureTheory WithLp
open scoped Matrix

namespace Work.LWP.BiotSavart

theorem farField_decay_const {ω : R3 → R3} {R M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hω : ∀ y, ‖ω y‖ ≤ M) (hsupp : ∀ y, ω y ≠ 0 → y ∈ Metric.closedBall 0 R) :
    ∀ x : R3, 2 * R ≤ ‖x‖ →
      ‖biotSavart ω x‖ ≤ (4 / 3) * M * R ^ 3 / ‖x‖ ^ 2 := by
  intro x hx
  -- the integrand of the Newtonian-potential Biot–Savart operator
  let W : R3 → R3 := fun y => WithLp.toLp 2 ((‖x - y‖ ^ (3:ℕ))⁻¹ • crossProduct (ω y) (x - y))
  have hbs : biotSavart ω x = (4 * Real.pi)⁻¹ • ∫ y, W y := rfl
  -- the integrand vanishes off `closedBall 0 R`
  have hzero : ∀ y, y ∉ Metric.closedBall (0:R3) R → W y = 0 := by
    intro y hy
    have hωy : ω y = 0 := by
      by_contra hne
      exact hy (hsupp y hne)
    simp only [W, hωy]
    simp
  have h1 : ‖(4 * Real.pi)⁻¹ • ∫ y, W y‖ = (4 * Real.pi)⁻¹ * ‖∫ y, W y‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h2 : ‖∫ y, W y‖ = ‖∫ y in Metric.closedBall (0:R3) R, W y‖ := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (f := W) hzero]
  -- the pointwise bound `‖W y‖ ≤ 4M/‖x‖²` on the ball
  have h3 : ‖∫ y in Metric.closedBall (0:R3) R, W y‖
      ≤ (4 / ‖x‖ ^ 2 * M) * Measure.real volume (Metric.closedBall (0:R3) R) := by
    apply norm_setIntegral_le_of_norm_le_const
    · rw [EuclideanSpace.volume_closedBall_fin_three]
      exact ENNReal.mul_lt_top (ENNReal.pow_lt_top (n := 3) ENNReal.ofReal_lt_top) ENNReal.ofReal_lt_top
    · intro y hy
      have hy' : ‖y‖ ≤ R := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hy
      exact integrand_norm_le hR hM hω hx hy'
  rw [hbs, h1, h2]
  calc (4 * Real.pi)⁻¹ * ‖∫ y in Metric.closedBall (0:R3) R, W y‖
      ≤ (4 * Real.pi)⁻¹ * ((4 / ‖x‖ ^ 2 * M) * Measure.real volume (Metric.closedBall (0:R3) R)) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = (4/3) * M * R^3 / ‖x‖^2 := by
        rw [volume_closedBall_real R hR]
        have hpi : (4 * Real.pi)⁻¹ * 4 * (Real.pi * 4 / 3) = (4/3 : ℝ) := by
          have h : (4 * Real.pi)⁻¹ * (4 * Real.pi) = 1 := inv_mul_cancel₀ (by positivity)
          calc (4 * Real.pi)⁻¹ * 4 * (Real.pi * 4 / 3)
              = ((4 * Real.pi)⁻¹ * (4 * Real.pi)) * (4/3) := by ring
            _ = 4/3 := by rw [h, one_mul]
        have hrewrite : (4 * Real.pi)⁻¹ * ((4 / ‖x‖ ^ 2 * M) * (R^3 * (Real.pi * 4 / 3)))
            = ((4*Real.pi)⁻¹ * 4 * (Real.pi*4/3)) * (M * R^3 * (‖x‖^2)⁻¹) := by
          rw [div_eq_mul_inv]
          ring
        rw [hrewrite, hpi]
        ring

end Work.LWP.BiotSavart
