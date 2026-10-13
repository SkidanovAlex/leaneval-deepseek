/-
Copyright: work module for the Elgindi finite-time singularity project.

# Vocabulary for the weak `cos²(2θ)`-weighted Hardy inequality (`cosSqHardyWeakFts`)

This file fixes the five functions of the flux argument that proves

  `∫_{Iθ} f² cos²(2θ) sin(2θ)^{-(2+η)} ≤ (1+η)^{-2} ∫_{Iθ} (f')² sin(2θ)^{-η}`

for `η ∈ [0,1)` and `f : ℝ → ℝ` of class `C²` on the *open* interval `(0,π/2)` with
`|f θ| ≤ M sin(2θ)` and `|f' θ| ≤ M` there.  The primitive

  `Φ θ = f θ² cos(2θ) sin(2θ)^{-(1+η)}`

has derivative `2G - 2B - 2(1+η)L` on `(0,π/2)`, where

* `L = f² cos²(2θ) sin(2θ)^{-(2+η)}` is the left hand integrand,
* `D = (f')² sin(2θ)^{-η}` is the right hand integrand,
* `B = f² sin(2θ)^{-η} ≥ 0` is the (nonnegative) middle term,
* `G = f f' cos(2θ) sin(2θ)^{-(1+η)}` is the cross term,

and `|G| ≤ ((1+η)/2) L + (1/(2(1+η))) D` pointwise (weighted AM–GM); `Φ → 0` at both
endpoints because `η < 1`, so the flux drops out of the fundamental theorem of calculus and
`(1+η)∫L = ∫G - ∫B ≤ ∫|G| ≤ ((1+η)/2)∫L + (1/(2(1+η)))∫D`.

The bounds `|f| ≤ M sin(2θ)`, `|f'| ≤ M` are what make every integrand honest:
each of `L`, `D`, `B`, `G` is dominated by `M² sin(2θ)^{-η}`, which is integrable on `Iθ`
from `-η > -1`.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngAWeak

set_option autoImplicit false

/-- The flux `Φ θ = f θ² cos(2θ) sin(2θ)^{-(1+η)}` of the Hardy argument. -/
def hardyFtsFlux (η : ℝ) (f : ℝ → ℝ) (θ : ℝ) : ℝ :=
  (f θ) ^ 2 * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-(1 + η))

/-- The left hand integrand `f² cos²(2θ) sin(2θ)^{-(2+η)}`. -/
def hardyFtsL (η : ℝ) (f : ℝ → ℝ) (θ : ℝ) : ℝ :=
  (f θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η))

/-- The right hand integrand `(f')² sin(2θ)^{-η}`. -/
def hardyFtsD (η : ℝ) (f : ℝ → ℝ) (θ : ℝ) : ℝ :=
  (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)

/-- The middle term `f² sin(2θ)^{-η}` (nonnegative). -/
def hardyFtsB (η : ℝ) (f : ℝ → ℝ) (θ : ℝ) : ℝ :=
  (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)

/-- The cross term `f f' cos(2θ) sin(2θ)^{-(1+η)}`. -/
def hardyFtsG (η : ℝ) (f : ℝ → ℝ) (θ : ℝ) : ℝ :=
  deriv f θ * f θ * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-(1 + η))

/-- `sin(2θ) > 0` on the open angular interval. -/
theorem hardyFts_sin_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `sin(2θ) ≥ 0` on the closed angular interval. -/
theorem hardyFts_sin_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- The set integral over `Iθ` is the integral over the open interval: the two sets differ by
the two endpoints, a null set. -/
theorem hardyFts_setIntegral_Iθ_eq_Ioo (G : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, G θ) = ∫ θ in Set.Ioo 0 (Real.pi / 2), G θ := by
  rw [Work.Spaces.Iθ]
  exact MeasureTheory.setIntegral_congr_set MeasureTheory.Ioo_ae_eq_Icc.symm

/-- The set integral over `Iθ` is the interval integral `0..π/2`. -/
theorem hardyFts_setIntegral_Iθ_eq_interval (G : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, G θ) = ∫ θ in (0 : ℝ)..(Real.pi / 2), G θ := by
  have hpi2 : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  rw [Work.Spaces.Iθ]
  exact ((intervalIntegral.integral_of_le hpi2).trans
    (MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioc_ae_eq_Icc (μ := volume)))).symm

end Work.FTS.EllipticEst.AngAWeak

end
