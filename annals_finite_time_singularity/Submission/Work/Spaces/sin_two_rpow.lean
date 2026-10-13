/-
Copyright: work module for the Elgindi finite-time singularity project.

# Integrability and a quantitative bound for `θ ↦ sin(2θ)^p` on `[0,π/2]`

This file proves

`IntegrableOn (fun θ => sin(2θ)^p) Iθ ∧ ∫_{Iθ} sin(2θ)^p ≤ 100/(p+1)`

for every `p` with `-1 < p ≤ 0`.  It is the angular estimate needed for the
weighted `L²`-Sobolev spaces of

T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
incompressible Euler equations on `ℝ³`*, Annals of Math. 194 (3) 2021.

## Mathematics

Write `q = -p ∈ [0,1)`.

* `p = 0`: the integrand is identically `1`, hence integrable, and the integral
  is the length `π/2 ≤ 100 = 100/(0+1)` of the interval.
* `-1 < p < 0`: the integrand is nonnegative on `Iθ` and has integrable
  endpoint singularities.  Jordan's inequality gives the pointwise majorant
  `sin(2θ)^{-q} ≤ (π/4)^q (θ^{-q} + (π/2 - θ)^{-q})` on `Iθ`
  (`Work.Spaces.sin_rpow_le_majorant_pi`), which is integrable
  (`Work.Spaces.integrableOn_majorant_rpow`) with integral
  `π (1/2)^q / (1 - q)` (`Work.Spaces.integral_majorant_rpow`).  Since
  `(1/2)^q ≤ 1` and `π ≤ 4`, this is at most `4/(1-q) = 4/(p+1) ≤ 100/(p+1)`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.sin_rpow_le_majorant_pi
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

theorem sin_two_rpow (p : ℝ) (hp : -1 < p) (hp0 : p ≤ 0) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ p) Work.Spaces.Iθ ∧
      ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ p ≤ 100 / (p + 1) := by
  rcases eq_or_lt_of_le hp0 with hp_eq | hp_lt
  · -- The exponent vanishes: the integrand is the constant `1`.
    subst hp_eq
    constructor
    · simpa only [Real.rpow_zero] using
        (MeasureTheory.integrableOn_const (μ := volume) (s := Work.Spaces.Iθ) (C := (1:ℝ))
          (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
    · have hvol : volume.real Work.Spaces.Iθ = Real.pi / 2 := by
        rw [MeasureTheory.measureReal_def, Work.Spaces.Iθ, Real.volume_Icc,
            ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
        ring
      have hconst : ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (0:ℝ)
          = volume.real Work.Spaces.Iθ := by
        simp only [Real.rpow_zero]
        rw [MeasureTheory.setIntegral_const]
        simp
      rw [hconst, hvol]
      norm_num
      linarith [Real.pi_le_four]
  · -- The exponent is negative: dominate by the integrable majorant.
    set q : ℝ := -p with hq
    have hq0 : 0 < q := by rw [hq]; linarith
    have hq1 : q < 1 := by rw [hq]; linarith
    have hpq : p = -q := by rw [hq]; ring
    -- The majorant, its integrability and its integral.
    have hGint : Integrable (fun θ : ℝ => (Real.pi/4)^q * (θ^(-q) + (Real.pi/2 - θ)^(-q)))
        (volume.restrict Work.Spaces.Iθ) := by
      rw [Work.Spaces.Iθ]; exact Work.Spaces.integrableOn_majorant_rpow q hq0 hq1
    have hGval : ∫ θ in Work.Spaces.Iθ, ((Real.pi/4)^q * (θ^(-q) + (Real.pi/2 - θ)^(-q)))
        = Real.pi * (1/2)^q / (1 - q) := by
      rw [Work.Spaces.Iθ]; exact Work.Spaces.integral_majorant_rpow q hq0 hq1
    -- Nonnegativity of the integrand on `Iθ`.
    have hnonneg : 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ] (fun θ : ℝ => (Real.sin (2*θ))^p) := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      exact Real.rpow_nonneg
        (Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) p
    -- The pointwise majorant `sin(2θ)^p ≤ G θ`.
    have hpoint : (fun θ : ℝ => (Real.sin (2*θ))^p) ≤ᵐ[volume.restrict Work.Spaces.Iθ]
        (fun θ : ℝ => (Real.pi/4)^q * (θ^(-q) + (Real.pi/2 - θ)^(-q))) := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      rw [hpq]
      exact Work.Spaces.sin_rpow_le_majorant_pi q θ hq0 hθ
    -- Measurability of the integrand (it is `sin ∘ (· * 2)` raised to a constant power).
    have hmeas : AEStronglyMeasurable (fun θ : ℝ => (Real.sin (2*θ))^p)
        (volume.restrict Work.Spaces.Iθ) :=
      (Measurable.pow_const (Real.measurable_sin.comp (measurable_const.mul measurable_id)) p)
        |>.aestronglyMeasurable
    -- Domination of the norms, as required by `Integrable.mono'`.
    have hnorm : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        ‖(Real.sin (2*θ))^p‖ ≤ (Real.pi/4)^q * (θ^(-q) + (Real.pi/2 - θ)^(-q)) := by
      filter_upwards [hpoint, hnonneg] with θ h1 h2
      rw [Real.norm_of_nonneg h2]
      exact h1
    constructor
    · exact hGint.mono' hmeas hnorm
    · calc ∫ θ in Work.Spaces.Iθ, (Real.sin (2*θ))^p
          ≤ ∫ θ in Work.Spaces.Iθ, ((Real.pi/4)^q * (θ^(-q) + (Real.pi/2 - θ)^(-q))) :=
            integral_mono_of_nonneg hnonneg hGint hpoint
        _ = Real.pi * (1/2)^q / (1 - q) := hGval
        _ ≤ 100 / (p + 1) := by
            rw [hpq]
            rw [show -q + 1 = 1 - q by ring]
            have hpi : Real.pi * (1/2:ℝ)^q ≤ 100 := by
              have h1 : (1/2:ℝ)^q ≤ 1 := Real.rpow_le_one (by norm_num) (by norm_num) (le_of_lt hq0)
              have h2 : Real.pi * (1/2:ℝ)^q ≤ Real.pi * 1 :=
                mul_le_mul_of_nonneg_left h1 (le_of_lt Real.pi_pos)
              linarith [Real.pi_le_four]
            exact div_le_div_of_nonneg_right hpi (by linarith)

end Work.Spaces
