/-
Copyright: work module for the Elgindi finite-time singularity project.

# The angular integral bound for the transfer `𝒲^{4,∞} → ℋ⁴`

Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021): in the
transfer from the weighted space `𝒲^{4,∞}` to `ℋ⁴` the `θ`-integration of the
two angular profiles has to be controlled by universal constants.  The two
factors occurring are

* `sin(2θ)^{-η}`, whose endpoint singularities are integrable on `Iθ = [0,π/2]`
  because `η = 99/100 < 1`, and whose integral is at most `10^4`; and
* `(α + sin 2θ)^2 · sin(2θ)^{2α/5 - γ(α)}` with `γ(α) = 1 + α/10`, whose
  integral is at most `700` uniformly in `α ∈ (0,1]`.

This file assembles those two estimates (proved in
`Submission.Work.Spaces.sin_two_rpow` and
`Submission.Work.Elliptic.WtoHAux`) into the single uniform bound
`∫_{Iθ} (A · sin(2θ)^{-η} + B · (α+sin 2θ)^2 sin(2θ)^{2α/5-γ}) ≤ A·10^4 + B·700`
for `A, B ≥ 0`.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Elliptic.WtoHAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic

open MeasureTheory

set_option autoImplicit false

/-- The angular part of the transfer estimate: on `Iθ` the sum of the two
weighted profiles with nonnegative coefficients is bounded by `A · 10^4 + B · 700`,
uniformly in `α ∈ (0,1]`. -/
theorem WtoH_Angular {α A B : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∫ θ in Work.Spaces.Iθ, (A * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        + B * ((α + Real.sin (2 * θ)) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)))
      ≤ A * 10 ^ 4 + B * 700 := by
  -- The exponent `-η` lies in `(-1, 0)`, so `sin(2θ)^{-η}` is integrable on `Iθ`.
  have hpe : (-1 : ℝ) < -(Work.Spaces.eta) := by rw [Work.Spaces.eta]; norm_num
  have hpe0 : -(Work.Spaces.eta) ≤ 0 := by rw [Work.Spaces.eta]; norm_num
  obtain ⟨hfint, hfb⟩ := Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) hpe hpe0
  -- Integrability of the two summands of the integrand.
  have hfint' : IntegrableOn (fun θ : ℝ => A * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ := hfint.const_mul A
  have hgint : IntegrableOn (fun θ : ℝ => B * ((α + Real.sin (2 * θ)) ^ 2
      * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))) Work.Spaces.Iθ :=
    (Work.Spaces.integrableOn_angular_weight' hα hα1).const_mul B
  -- The two `α`-free quadrature bounds: `100 / (-η + 1) = 10^4` and `700`.
  have hfb' : ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) ≤ 10 ^ 4 := by
    refine le_trans hfb ?_
    rw [Work.Spaces.eta]
    norm_num
  have hgb : ∫ θ in Work.Spaces.Iθ, ((α + Real.sin (2 * θ)) ^ 2
      * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)) ≤ 700 :=
    Work.Spaces.angular_weight_integral_bound' hα hα1
  calc ∫ θ in Work.Spaces.Iθ, (A * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        + B * ((α + Real.sin (2 * θ)) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)))
      = A * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        + B * (∫ θ in Work.Spaces.Iθ, ((α + Real.sin (2 * θ)) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))) := by
        rw [integral_add hfint' hgint, integral_const_mul, integral_const_mul]
    _ ≤ A * 10 ^ 4 + B * 700 := by
        have h1 := mul_le_mul_of_nonneg_left hfb' hA
        have h2 := mul_le_mul_of_nonneg_left hgb hB
        linarith

end Work.Elliptic
