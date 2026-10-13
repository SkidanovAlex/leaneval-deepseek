/-
Copyright: work module for the Elgindi finite-time singularity project.

# The vocabulary of `slice_ibp_sigma`

This module owns the functions of the one-dimensional integration by parts
`Work.FTS.EllipticEst.AngSecond.slice_ibp_sigma`, the angular identity

  `∫_θ (f')² σ = -∫_θ f f'' σ + 2η ∫_θ f² σ + 2η(1+η) ∫_θ f² cos²(2θ) sin(2θ)^{-(2+η)}`

for the angular weight `σ θ = sin(2θ)^{-η}` (`0 ≤ η < 1`), integrated over
`Work.Spaces.Iθ = [0,π/2]`:

* `sigE η θ = sin(2θ)^{-η}`                                        (`σ`),
* `sigD η θ = -2η cos(2θ) sin(2θ)^{-(1+η)}`                        (`σ'`),
* `sigDD η θ = 4η σ θ + 4η(1+η) cos²(2θ) sin(2θ)^{-(2+η)}`         (`σ''`),

together with the shorthands `s2 θ = sin(2θ)`, `c2 θ = cos(2θ)`.

The derivatives `sigD` and `sigDD` are only the genuine derivatives of `sigE` on the
*open* interval `(0,π/2)` (at the two endpoints `sin(2θ)^{-η}` has an infinite one-sided
derivative), which is exactly where the integration by parts uses them.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllipticEst.AngSecond.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngSecond

set_option autoImplicit false

/-- `s2 θ = sin(2θ)`. -/
def s2 (θ : ℝ) : ℝ := Real.sin (2 * θ)

/-- `c2 θ = cos(2θ)`. -/
def c2 (θ : ℝ) : ℝ := Real.cos (2 * θ)

/-- The angular weight `sigE η θ = sin(2θ)^{-η}` of `slice_ibp_sigma`. -/
def sigE (η θ : ℝ) : ℝ := Real.sin (2 * θ) ^ (-η)

/-- The derivative of `sigE η` on the open interval:
`sigD η θ = -2η cos(2θ) sin(2θ)^{-(1+η)}`. -/
def sigD (η θ : ℝ) : ℝ := -2 * η * Real.cos (2 * θ) * Real.sin (2 * θ) ^ (-(1 + η))

/-- The second derivative of `sigE η` on the open interval:
`sigDD η θ = 4η sin(2θ)^{-η} + 4η(1+η) cos²(2θ) sin(2θ)^{-(2+η)}`. -/
def sigDD (η θ : ℝ) : ℝ :=
  4 * η * sigE η θ
    + 4 * η * (1 + η) * Real.cos (2 * θ) ^ 2 * Real.sin (2 * θ) ^ (-(2 + η))

@[simp] theorem s2_apply (θ : ℝ) : s2 θ = Real.sin (2 * θ) := rfl
@[simp] theorem c2_apply (θ : ℝ) : c2 θ = Real.cos (2 * θ) := rfl
@[simp] theorem sigE_apply (η θ : ℝ) : sigE η θ = Real.sin (2 * θ) ^ (-η) := rfl
@[simp] theorem sigD_apply (η θ : ℝ) :
    sigD η θ = -2 * η * Real.cos (2 * θ) * Real.sin (2 * θ) ^ (-(1 + η)) := rfl
@[simp] theorem sigDD_apply (η θ : ℝ) :
    sigDD η θ = 4 * η * sigE η θ
      + 4 * η * (1 + η) * Real.cos (2 * θ) ^ 2 * Real.sin (2 * θ) ^ (-(2 + η)) := rfl

/-- Near an interior point the weight `sigE η` is positive. -/
theorem sigE_pos {η θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) : 0 < sigE η θ := by
  rw [sigE_apply]
  exact Real.rpow_pos_of_pos
    (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])) _

/-- The set integral over `Work.Spaces.Iθ = [0,π/2]` is the interval integral `0..π/2`. -/
theorem setIntegral_Iθ_eq_interval (g : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, g θ) = ∫ θ in (0 : ℝ)..(Real.pi / 2), g θ := by
  have hpi2 : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  rw [Work.Spaces.Iθ]
  exact ((intervalIntegral.integral_of_le hpi2).trans
    (MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioc_ae_eq_Icc (μ := volume)))).symm

end Work.FTS.EllipticEst.AngSecond
