/-
Copyright: work module for the Elgindi finite-time singularity project.

# `WPQ`: the interior (`SmoothQuad`) `𝒲^{4,∞}`-`ℋ⁴` product rule

This module holds the *definitions* used by the pieces of the proof of
`Work.FTS.H2.WProdQ` (`Submission/Work/FTS/H2/WProdQ.lean`), the `RegQ` version of Elgindi's
`WProductRule` (tex 1086).

The delivered proof of `Work.Spaces.WProductRule` estimates the `ℋ⁴`-integrand of the product
`f·g` pointwise by `10^14 |f|_{𝒲^{4,∞}}² · Gmaj α g`, where

`Gmaj α g = HkIntegrand α 4 g + (γ-1)⁻¹ (∑_{d<4} Btil α g d) · ((α+sin2θ)² sin(2θ)^{2α/5-γ} w²)`

and `Btil α g d z = ∫_θ (∂_θ D_z^d g)² sin(2θ)^{2-γ}`.  The whole majorant-integrability
apparatus around `Btil` (the identity `w² Btil = ∫(D_z^d D_θ g · W)²`, the radial weight
`w²` bookkeeping, `integrableOn_Btil_w`, `integrableOn_Gmaj`, ...) can be avoided by
*integrating the angular variable first* and keeping the angular `L²`-norm of the mixed slot
as a single quantity: with

`Aang α g d z := ∫_θ (D_z^d D_θ g(z,θ) · W(z,θ))²`

the Hardy bound `(D_z^d g · w)² ≤ 100/(γ-1) · Aang α g d z` replaces the `Btil` form, and the
whole majorant is the function `GmajQ` below.  Two elementary facts then replace the Fubini
apparatus:

* `∑_{d<4} Aang α g d z ≤ 4 ∫_θ HkIntegrand α 4 g z θ` (pointwise in `z`), and
* `HkSq α 4 (fg) ≤ ∫_z 10^14 |f|_𝒲² (1 + 2800/(γ-1)) (∫_θ HkIntegrand α 4 g z θ)`,

whose right-hand side is integrable by `HkMem α 4 g` alone — no measurability of the
`z ↦ Aang ... z` is ever needed.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.WProductRule
import Submission.Work.FTS.LocData.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.WPQ

set_option autoImplicit false

/-- `Aang α g d z = ∫_θ (D_z^d D_θ g(z,θ) · W(z,θ))²`, the squared angular `L²`-norm (with the
`ℋ⁴` weight `W = w·sin(2θ)^{-γ/2}`) of the mixed slot `D_z^d D_θ g`, at fixed `z`. -/
def Aang (α : ℝ) (g : ℝ → ℝ → ℝ) (d : ℕ) (z : ℝ) : ℝ :=
  ∫ σ in Work.Spaces.Iθ, (Work.Spaces.mixed d 1 g z σ * Work.Spaces.Wt α z σ) ^ 2

/-- The pointwise majorant of the product rule for the *pairing-free* form of the estimate:

`HkIntegrand α 4 (f·g) z θ ≤ 10^14 |f|_𝒲² GmajQ α g z θ`.

Here `GmajQ α g` is the `ℋ⁴`-integrand of `g` plus the angular-Hardy contribution
`(γ-1)⁻¹ (∑_{d<4} Aang α g d z) · (α+sin2θ)² sin(2θ)^{2α/5-γ}`. -/
def GmajQ (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  Work.Spaces.HkIntegrand α 4 g z θ + (Work.Spaces.gam α - 1)⁻¹
    * (∑ d ∈ Finset.range 4, Aang α g d z)
    * ((α + Real.sin (2 * θ)) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))

/-! ## Elementary facts -/

theorem Aang_nonneg (α : ℝ) (g : ℝ → ℝ → ℝ) (d : ℕ) (z : ℝ) : 0 ≤ Aang α g d z :=
  setIntegral_nonneg measurableSet_Icc fun σ _ => sq_nonneg _

theorem sum_Aang_nonneg (α : ℝ) (g : ℝ → ℝ → ℝ) (z : ℝ) :
    0 ≤ ∑ d ∈ Finset.range 4, Aang α g d z :=
  Finset.sum_nonneg fun d _ => Aang_nonneg α g d z

/-- The `θ`-factor of the angular-Hardy contribution is nonnegative on `Iθ`. -/
theorem theta_factor_nonneg {α θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ (α + Real.sin (2 * θ)) ^ 2
      * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α) :=
  mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Work.Spaces.sin_two_nonneg' hθ) _)

theorem GmajQ_nonneg {α : ℝ} (hα : 0 < α) (g : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ GmajQ α g z θ := by
  have hγ1 : (0 : ℝ) < Work.Spaces.gam α - 1 := by
    rw [Work.Spaces.gam_sub_one]; linarith
  simp only [GmajQ]
  exact add_nonneg (Work.Spaces.HkIntegrand_nonneg α 4 g z θ)
    (mul_nonneg (mul_nonneg (inv_nonneg.mpr hγ1.le) (sum_Aang_nonneg α g z))
      (theta_factor_nonneg hθ))

theorem sin_two_pos_of_Ioo {θ : ℝ} (h : θ ∈ Set.Ioo 0 (π / 2)) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [h.1]) (by linarith [h.2, Real.pi_pos])

/-- On the open quadrant, `(W)² = w² sin(2θ)^{-γ}`.  (The exponent bookkeeping is done with
`Real.rpow_add` against the *positive* base `sin(2θ)`.) -/
theorem Wt_sq_of_Ioo (α z θ : ℝ) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  have hs : 0 < Real.sin (2 * θ) := sin_two_pos_of_Ioo hθ
  have hstep : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [pow_two, ← Real.rpow_add hs]
    congr 1
    ring
  simp only [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow, hstep]

/-- The `ℋ^k`-integrand vanishes whenever `sin(2θ) = 0`: both weights carry a factor
`sin(2θ)^{c}` with `c > 0` (Lean's totalised `x ^ y` is `0` at `x = 0` for `y ≠ 0`). -/
theorem HkIntegrand_eq_zero_of_sin_two_eq_zero {α : ℝ} (hα : Work.Spaces.gam α ≠ 0)
    {F : ℝ → ℝ → ℝ} {z θ : ℝ} (h : Real.sin (2 * θ) = 0) :
    Work.Spaces.HkIntegrand α 4 F z θ = 0 := by
  have hη : (Work.Spaces.eta / 2 : ℝ) ≠ 0 := by norm_num [Work.Spaces.eta]
  have hg : -(Work.Spaces.gam α / 2) ≠ 0 := by
    intro hc
    exact hα (by linarith [neg_eq_zero.mp hc])
  simp only [Work.Spaces.HkIntegrand, Work.Spaces.Wt, Work.Spaces.wTheta]
  rw [h, Real.zero_rpow hη, Real.zero_rpow hg]
  simp

end Work.FTS.H2.WPQ
