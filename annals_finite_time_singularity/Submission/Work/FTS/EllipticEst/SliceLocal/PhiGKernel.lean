/-
Copyright: work module for the Elgindi finite-time singularity project.

# The kernel vocabulary of the `PhiG` bounds

`Work.FTS.EllipticEst.SliceLocal.PhiG g θ = (2 cos³θ)⁻¹ ∫_θ^{π/2} sin σ cos²σ g σ dσ`
is the data-determined angular function of the slice interior estimate.  This module fixes the
notation used to bound it:

* `Kkern θ  = sin θ cos²θ` — the kernel of the integral;
* `Kcoef θ  = (2 cos³θ)⁻¹` — the prefactor, so `PhiG g θ = Kcoef θ * Qg g θ`;
* `Qg g θ   = ∫_θ^{π/2} Kkern σ g σ dσ` — the (weighted) cumulative integral of the data;
* `Wg θ     = ∫_θ^{π/2} Kkern σ² / sEta σ dσ` — the `L²` norm-squared of the kernel over the
  remaining angular interval, i.e. the weight against which the data energy is measured;
* `PhiDen θ = Kcoef θ * sqrt (Wg θ)` — the *density* of `PhiG`: Cauchy–Schwarz gives
  `|PhiG g θ| ≤ PhiDen θ * sqrt (∫_{Iθ} g² sEta)`;
* `Ene g    = ∫_{Iθ} g² sEta` — the data energy.

The whole content of `PhiG_bounds` is then (i) the Cauchy–Schwarz step
`|Qg g θ| ≤ sqrt (Wg θ) * sqrt (Ene g)` and (ii) the explicit bounds on the kernel density
`PhiDen` (which involve no `g` at all).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.SliceLocal.Defs
import Submission.Work.FTS.EllipticEst.TT.SliceCoercDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.SliceLocal

set_option autoImplicit false

/-- The kernel `sin θ cos²θ` of the `PhiG` integral. -/
def Kkern (θ : ℝ) : ℝ := Real.sin θ * (Real.cos θ) ^ 2

/-- The prefactor `(2 cos³θ)⁻¹` of `PhiG`, so that `PhiG g θ = Kcoef θ * Qg g θ`. -/
def Kcoef (θ : ℝ) : ℝ := (2 * (Real.cos θ) ^ 3)⁻¹

/-- The cumulative integral `∫_θ^{π/2} sin σ cos²σ · g σ dσ` of the data. -/
def Qg (g : ℝ → ℝ) (θ : ℝ) : ℝ :=
  ∫ σ in θ..(Real.pi / 2), Kkern σ * g σ

/-- The `L²`-weight of the kernel over the angular tail `[θ, π/2]`. -/
def Wg (θ : ℝ) : ℝ :=
  ∫ σ in θ..(Real.pi / 2), (Kkern σ) ^ 2 / Work.FTS.EllipticEst.sEta σ

/-- The density of `PhiG`: the Cauchy–Schwarz factor multiplying `sqrt (Ene g)`. -/
def PhiDen (θ : ℝ) : ℝ := Kcoef θ * Real.sqrt (Wg θ)

/-- The data energy `∫_{Iθ} g² sEta`. -/
def Ene (g : ℝ → ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ

/-- The defining identity `PhiG g θ = Kcoef θ * Qg g θ`. -/
theorem PhiG_eq_Kcoef_mul_Qg (g : ℝ → ℝ) :
    PhiG g = fun θ => Kcoef θ * Qg g θ := rfl

/-- `PhiG g θ = Kcoef θ * Qg g θ`, applied form. -/
theorem PhiG_apply (g : ℝ → ℝ) (θ : ℝ) : PhiG g θ = Kcoef θ * Qg g θ := rfl

/-- `sEta` is nonnegative on `Iθ`. -/
theorem sEta_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.sEta θ :=
  Real.rpow_nonneg (Work.FTS.EllipticEst.TT.sin_two_nonneg hθ) _

/-- The reciprocal of the weight `sEta` is the familiar `sin(2θ)^η`; this is the form in which
the kernel weight `Wg` is estimated. -/
theorem inv_sEta_eq {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.FTS.EllipticEst.sEta θ)⁻¹ = (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := by
  rw [Work.FTS.EllipticEst.sEta,
    Real.rpow_neg (Work.FTS.EllipticEst.TT.sin_two_nonneg hθ), inv_inv]

/-- The integrand of `Wg` in the form used for the pointwise estimates. -/
theorem Kkern_sq_div_sEta {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Kkern θ) ^ 2 / Work.FTS.EllipticEst.sEta θ
      = (Real.sin θ) ^ 2 * (Real.cos θ) ^ 4
          * (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := by
  rw [Kkern, div_eq_mul_inv, inv_sEta_eq hθ]
  ring

/-- `Wg` is nonnegative (for `θ ≤ π/2`, so that the interval of integration is traversed
forwards). -/
theorem Wg_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Wg θ := by
  rw [Wg]
  refine intervalIntegral.integral_nonneg hθ.2 fun σ hσ => ?_
  refine div_nonneg (sq_nonneg _) ?_
  exact sEta_nonneg ⟨le_trans hθ.1 hσ.1, hσ.2⟩

/-- `Kcoef` is nonnegative on `Iθ`. -/
theorem Kcoef_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Kcoef θ := by
  rw [Kcoef]
  refine inv_nonneg.2 (mul_nonneg (by norm_num) ?_)
  exact pow_nonneg (Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hθ.1, Real.pi_pos], by linarith [Real.pi_pos, hθ.2]⟩) 3

end Work.FTS.EllipticEst.SliceLocal
