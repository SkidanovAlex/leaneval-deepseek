import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Coercivity.thetaAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

/-- The angular factor `cos(2θ)·sin(2θ)^{-γ}` is integrable against `(v z θ)^2` on `Iθ`
as soon as the weight-`w(z)^2` version `thetaW α z θ·(v z θ)^2` is: on `0 < z` the
constant `w(z)^2` is nonzero (so it can be divided out), and `cos(2·)` is continuous,
hence bounded, on the compact interval `Iθ`. -/
theorem cos_sin_integrable (α : ℝ) (v : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd v)
    (z : ℝ) (hz : 0 < z)
    (hC : MeasureTheory.IntegrableOn (fun θ => Work.Coercivity.thetaW α z θ * (v z θ) ^ 2) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ => Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * (v z θ) ^ 2) Work.Spaces.Iθ := by
  -- On `0 < z` the weight `w z = (1+z)^2/z^2` does not vanish.
  have hw : Work.Spaces.w z ≠ 0 := by
    unfold Work.Spaces.w
    positivity
  -- Divide the constant `w z ^ 2` out of the hypothesis: the bare weight
  -- `sin(2θ)^{-γ}·(v z θ)^2` is integrable.
  have hg : MeasureTheory.IntegrableOn
      (fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * (v z θ) ^ 2) Work.Spaces.Iθ := by
    rw [MeasureTheory.IntegrableOn] at hC ⊢
    have hrw : (fun θ => Work.Coercivity.thetaW α z θ * (v z θ) ^ 2)
        = fun θ => (Work.Spaces.w z) ^ 2 *
            ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * (v z θ) ^ 2) := by
      funext θ
      simp only [Work.Coercivity.thetaW]
      ring
    rw [hrw] at hC
    exact (MeasureTheory.integrable_const_mul_iff
      (isUnit_iff_ne_zero.mpr (pow_ne_zero 2 hw)) _).mp hC
  -- `cos(2·)` is continuous on the compact interval `Iθ`, hence bounded there, so it
  -- may be multiplied against the integrable function.
  have hcont : ContinuousOn (fun θ : ℝ => Real.cos (2 * θ)) Work.Spaces.Iθ :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn
  have hK : IsCompact Work.Spaces.Iθ := isCompact_Icc
  have hh := MeasureTheory.IntegrableOn.continuousOn_mul hcont hg hK
  simpa [mul_assoc] using hh

end Work.Coercivity
