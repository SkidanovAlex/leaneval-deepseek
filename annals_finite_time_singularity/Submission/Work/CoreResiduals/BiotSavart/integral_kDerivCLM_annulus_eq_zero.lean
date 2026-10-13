import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.StabilityFar.Decay.KernelDefs
import Submission.Work.CoreResiduals.BiotSavart.KfBall.sphere_integral_inner_smul
import Submission.Work.CoreResiduals.BiotSavart.KfBall.sphere_integral_even_smul_eq_zero
import Submission.Work.CoreResiduals.BiotSavart.KfBall.integrableOn_kf_ball
import Submission.Work.CoreResiduals.BiotSavart.kf_ball_integral
import Submission.Work.CoreResiduals.BiotSavart.KfBall.inner_add_sqrt_pos
import Submission.Work.CoreResiduals.BiotSavart.integrable_indicator_kDerivCLM_annulus
import Submission.Work.CoreResiduals.BiotSavart.ray_indicator_kDerivCLM
import Submission.Work.CoreResiduals.BiotSavart.sphere_integral_kDerivCLM_angular

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open MeasureTheory Metric Set
open scoped ENNReal NNReal Topology

-- The hypothesis `hrρ : r < ρ` of the statement below is not needed by the argument (the
-- polar-coordinate computation covers the degenerate case `ρ ≤ r` just as well); silence the
-- unused-variable linter so that the requested statement can be kept verbatim.
set_option linter.unusedVariables false

/-- **The exact kernel-mass identity on a centred annulus.**

The derivative of the Newtonian kernel, `Work.StabilityFar.Decay.kDerivCLM b = ‖b‖⁻³ • Id − 3‖b‖⁻⁵ • (innerSL ℝ b).smulRight b`, has zero Bochner integral over any annulus `r < ‖b‖ < ρ` centred at the origin.

In polar coordinates `b = s ν` the integrand is `s⁻³ (Id − 3 ν⊗ν)` and `db = s² ds dσ`, so the integral is `(∫_r^ρ s⁻¹ ds) • ∫_{S²}(Id − 3ν⊗ν) dσ`, and the angular factor has zero spherical mean: `4π • Id − 3 • (4π/3) • Id = 0` (the second moment identity, as used in `Work.CoreResiduals.BiotSavart.KfBall.sphere_integral_inner_smul`).  The hypothesis `0 < r` is what makes the radial factor finite; the integrand is continuous on the closed annulus, hence Bochner integrable.

This identity is what kills the logarithmic divergence of the kernel masses in Calderón–Zygmund difference estimates: it lets one replace `ω a - ω x` by `ω a - V` for any constant `V` inside a peeled integral over a centred annulus, and bounds the far-field kernel mass by a constant instead of a logarithm. -/
theorem integral_kDerivCLM_annulus_eq_zero {r ρ : ℝ} (hr : 0 < r) (hrρ : r < ρ) :
    ∫ b in (Metric.ball (0 : Work.LWP.R3) ρ) \ (Metric.ball (0 : Work.LWP.R3) r),
      Work.StabilityFar.Decay.kDerivCLM b = 0 := by
  classical
  -- The Bochner integral of the `R3 →L[ℝ] R3`-valued integrand goes through
  -- `MeasureTheory.integral_smul_const` (pulling out the angular factor), which needs the
  -- codomain to be complete; here it is even finite dimensional.
  have hComplete : CompleteSpace (Work.LWP.R3 →L[ℝ] Work.LWP.R3) :=
    FiniteDimensional.complete ℝ (Work.LWP.R3 →L[ℝ] Work.LWP.R3)
  set A : Set Work.LWP.R3 := Metric.ball (0 : Work.LWP.R3) ρ \ Metric.ball (0 : Work.LWP.R3) r
  have hmeas : MeasurableSet A := measurableSet_ball.diff measurableSet_ball
  -- Integrability of the integrand on the annulus (the content of the hypothesis `0 < r`).
  have hint : Integrable (A.indicator (fun b => Work.StabilityFar.Decay.kDerivCLM b)) volume :=
    integrable_indicator_kDerivCLM_annulus (ρ := ρ) hr
  -- Write the set integral as the integral of the indicator against Lebesgue measure ...
  rw [← integral_indicator hmeas (f := fun b => Work.StabilityFar.Decay.kDerivCLM b)]
  -- ... and pass to polar coordinates: `ℝ³ ≃ S² × (0,∞)`, `(ω,s) ↦ s • ω`.
  rw [integral_polar hint]
  -- On each ray the annulus is the interval `[r,ρ)` and the integrand separates into a radial
  -- factor and the fixed angular factor `Id − 3 ν⊗ν`.
  have hinner : ∀ ω : Metric.sphere (0 : Work.LWP.R3) 1,
      (∫ s : Set.Ioi (0 : ℝ),
          A.indicator (fun b => Work.StabilityFar.Decay.kDerivCLM b)
            ((s : ℝ) • (ω : Work.LWP.R3))
          ∂(Measure.volumeIoiPow 2))
        = (∫ s : Set.Ioi (0 : ℝ),
              (if r ≤ (s : ℝ) ∧ (s : ℝ) < ρ then (((s : ℝ)) ^ 3)⁻¹ else 0)
              ∂(Measure.volumeIoiPow 2))
            • (ContinuousLinearMap.id ℝ Work.LWP.R3
                - (3 : ℝ) • (innerSL ℝ (ω : Work.LWP.R3)).smulRight
                    (ω : Work.LWP.R3)) := by
    intro ω
    have hcongr : (fun s : Set.Ioi (0 : ℝ) => A.indicator
          (fun b => Work.StabilityFar.Decay.kDerivCLM b) ((s : ℝ) • (ω : Work.LWP.R3)))
        = fun s : Set.Ioi (0 : ℝ) =>
            (if r ≤ (s : ℝ) ∧ (s : ℝ) < ρ then (((s : ℝ)) ^ 3)⁻¹ else 0)
              • (ContinuousLinearMap.id ℝ Work.LWP.R3
                  - (3 : ℝ) • (innerSL ℝ (ω : Work.LWP.R3)).smulRight
                      (ω : Work.LWP.R3)) := by
      funext s
      exact ray_indicator_kDerivCLM s ω
    rw [hcongr, integral_smul_const]
  simp_rw [hinner]
  -- The radial factor is a constant, and the angular factor integrates to zero.
  rw [integral_smul, sphere_integral_kDerivCLM_angular, smul_zero]

end Work.CoreResiduals.BiotSavart
