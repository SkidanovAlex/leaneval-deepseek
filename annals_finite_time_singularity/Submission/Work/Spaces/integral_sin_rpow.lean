/-
Copyright: work module for the Elgindi finite-time singularity project.

# The angular integral `∫_{[0,π/2]} sin(2θ)^{γ-2} dθ`

This file proves the bound

`∫ θ in [0,π/2], sin(2θ)^{γ-2} ≤ 100/(γ-1)`   (`γ = gam α = 1 + α/10`, `0 < α ≤ 1`)

used in the weighted-function-space estimates of

T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
incompressible Euler equations on `ℝ³`*, Annals of Math. 194 (3) 2021.

## Mathematics

Write `p = 1 - α/10 ∈ [9/10, 1)`.  Then `gam α - 2 = -p` and `gam α - 1 = 1 - p = α/10`,
so the claim is `∫₀^{π/2} sin(2θ)^{-p} dθ ≤ 100/(1-p)`.

* On `[0, π/4]` the chord bound `sin x ≥ 2x/π` (`x = 2θ`) gives `sin(2θ) ≥ 4θ/π`, hence
  `sin(2θ)^{-p} ≤ (π/(4θ))^p = (π/4)^p θ^{-p}`; dually `sin(2θ) = sin(2(π/2-θ)) ≥
  4(π/2-θ)/π` on `[π/4, π/2]`.  Putting both halves together gives the pointwise
  majorant `sin(2θ)^{-p} ≤ (π/4)^p (θ^{-p} + (π/2-θ)^{-p})` on `Iθ` (this is
  `Work.Spaces.sin_rpow_le_majorant`).
* The majorant is integrable on `Iθ` (`p < 1`) and its integral is, by symmetry and the
  elementary antiderivative of `x^{-p}`,
  `(π/4)^p · 2 (π/2)^{1-p}/(1-p) = π (1/2)^p/(1-p) ≤ 100/(1-p)`.

The majorant bound, its integrability and its integral are proved in the companion
modules `sin_rpow_le_majorant`, `integrableOn_majorant_rpow` and
`integral_majorant_rpow`; the present file assembles them into the target estimate.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.sin_rpow_le_majorant
import Submission.Work.Spaces.integrableOn_majorant_rpow
import Submission.Work.Spaces.integral_majorant_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false

/-- The angular integral of `sin(2θ)^{γ-2}` over `[0,π/2]` is bounded by `100/(γ-1)`
for `0 < α ≤ 1` (so that `1 < γ ≤ 11/10`, i.e. `γ - 1 = α/10 ≤ 1/10`).

The exponent `γ-2 = -(1 - α/10)` lies in `(-1, -9/10]`, so the integrand has an
integrable singularity at each endpoint `θ = 0` and `θ = π/2`; the sharp value of the
integral is `(√π/2) Γ((γ-1)/2)/Γ(γ/2) ≈ 1/(γ-1)` for `γ → 1⁺`, so the constant `100`
is very generous. -/
theorem integral_sin_rpow (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.gam α - 2)
      ≤ 100 / (Work.Spaces.gam α - 1) := by
  -- The exponent `gam α - 2 = -p` with `p = 1 - α/10 ∈ (0,1)`.
  set p : ℝ := 1 - α / 10 with hpdef
  have hp0 : 0 < p := by simp only [hpdef]; linarith
  have hp1 : p < 1 := by simp only [hpdef]; linarith
  have hexp : Work.Spaces.gam α - 2 = -p := by simp only [hpdef, Work.Spaces.gam]; ring
  have hgam : Work.Spaces.gam α - 1 = 1 - p := by simp only [hpdef, Work.Spaces.gam]; ring
  -- The majorant `G θ = (π/4)^p (θ^{-p} + (π/2-θ)^{-p})`: integrable with integral
  -- `π (1/2)^p / (1-p)`.
  have hGint : Integrable
      (fun θ : ℝ => (Real.pi / 4) ^ p * (θ ^ (-p) + (Real.pi / 2 - θ) ^ (-p)))
      (volume.restrict Work.Spaces.Iθ) := integrableOn_majorant_rpow p hp0 hp1
  have hGval : ∫ θ in Work.Spaces.Iθ,
        ((Real.pi / 4) ^ p * (θ ^ (-p) + (Real.pi / 2 - θ) ^ (-p)))
      = Real.pi * (1 / 2) ^ p / (1 - p) := integral_majorant_rpow p hp0 hp1
  -- The integrand is nonnegative on `Iθ`.
  have hnonneg : 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (Work.Spaces.gam α - 2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [hexp]
    exact Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) _
  -- The pointwise majorant, valid everywhere on `Iθ`.
  have hle : (fun θ : ℝ => (Real.sin (2 * θ)) ^ (Work.Spaces.gam α - 2)) ≤ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => (Real.pi / 4) ^ p * (θ ^ (-p) + (Real.pi / 2 - θ) ^ (-p))) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [hexp]
    exact sin_rpow_le_majorant p θ hp0 hθ
  have hmono := integral_mono_of_nonneg hnonneg hGint hle
  calc ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.gam α - 2)
      ≤ ∫ θ in Work.Spaces.Iθ, ((Real.pi / 4) ^ p * (θ ^ (-p) + (Real.pi / 2 - θ) ^ (-p))) :=
        hmono
    _ = Real.pi * (1 / 2) ^ p / (1 - p) := hGval
    _ ≤ 100 / (Work.Spaces.gam α - 1) := by
        rw [hgam]
        refine div_le_div_of_nonneg_right ?_ (by linarith : (0 : ℝ) ≤ 1 - p)
        have hhalf : (1 / 2 : ℝ) ^ p ≤ 1 :=
          Real.rpow_le_one (by norm_num) (by norm_num) (le_of_lt hp0)
        have h4 := Real.pi_lt_four
        have hnum : Real.pi * (1 / 2) ^ p ≤ 4 := by
          calc Real.pi * (1 / 2) ^ p ≤ 4 * 1 :=
                mul_le_mul (le_of_lt h4) hhalf (by positivity) (by norm_num)
            _ = 4 := by norm_num
        linarith

end Work.Spaces
