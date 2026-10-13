/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Fstar_approx`: the angular moment of the truncated approximation vanishes

`Work.FTS.PhiStar.Honesty.CptApp.approx n F` is the cut-off approximation of a source `F` used
by `Work.FTS.PhiStar.Honesty.exists_cptQ_approx`: with `chiR` the radial cutoff, `zetaR` the
angular cutoff and `rho` the (normalised) moment profile,

`approx n F z θ = chiR n z * (zetaR n θ * F z θ - lam n F z * rho θ)`,

where `lam n F z = ∫_θ zetaR n θ · F z θ · sinθcos²θ dθ` is the truncated angular moment.  The
subtraction of `lam n F z · rho θ` neutralises the angular moment: the class of sources to which
the weak-class elliptic node applies is the one whose angular moment

`F_* G z = ∫_θ G z θ · sinθcos²θ dθ`

vanishes identically (the `F_* F ≡ 0` of the paper).  This file proves that the approximation
inherits the property: `F_* (approx n F) z = 0` for every `z > 0`, with no hypothesis beyond the
normalisation `∫_θ rho θ · sinθcos²θ = 1` of the moment profile (which is what
`rho = crho⁻¹ * rhoAux` is for).

## The computation

`F_* (approx n F) z = ∫_θ chiR n z * (X θ - Y θ) = chiR n z * (∫_θ X θ - ∫_θ Y θ)`, where

`X θ = zetaR n θ * F z θ * sinθcos²θ` and `Y θ = lam n F z * (rho θ * sinθcos²θ)`.

By definition `lam n F z = ∫_θ X θ`, and
`∫_θ Y θ = lam n F z * ∫_θ rho θ · sinθcos²θ = lam n F z`, because `rho` is normalised.  The
bracket is therefore `lam n F z - lam n F z = 0`.

The only subtlety is the additivity of the integral: Mathlib's `integral_sub` needs *both*
integrands to be integrable.  `Y` always is (a constant times the continuous, compactly
supported profile `rho · sinθcos²θ`).  If `X` is *not* integrable then both `∫_θ X θ` and
`∫_θ (X - Y) θ` are the junk value `0` (`MeasureTheory.integral_undef`), so the identity still
holds; the proof therefore splits on `Integrable X`.

Everything is proved from the definitions of `CptApp/Defs.lean`; the hypotheses `HkMem α k F`
and `2 ≤ n` of the statement are not needed.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.PhiStar.Honesty.CptApp.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.CptApp

set_option autoImplicit false

/-! ## The smoothness, sign and size of the moment profile -/

/-- `rhoAux θ = cut01 (2θ - 2) * cut01 (3 - 2θ)` is nonnegative everywhere. -/
private theorem rhoAux_nonneg (θ : ℝ) : 0 ≤ rhoAux θ := by
  rw [rhoAux, cut01]
  exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

/-- `rhoAux` is strictly positive on its support `(1, 3/2)`. -/
private theorem rhoAux_pos_of_mem {θ : ℝ} (h0 : 1 < θ) (h1 : θ < 3 / 2) : 0 < rhoAux θ := by
  rw [rhoAux, cut01]
  exact mul_pos (Real.smoothTransition.pos_of_pos (by linarith))
    (Real.smoothTransition.pos_of_pos (by linarith))

/-- `sinθcos²θ` is nonnegative on the closed quadrant `[0, π/2]`. -/
private theorem sinCos2_nonneg_of_mem {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ π / 2) :
    0 ≤ Work.Elliptic.sinCos2 θ := by
  rw [Work.Elliptic.sinCos2]
  exact mul_nonneg (Real.sin_nonneg_of_mem_Icc ⟨h0, by linarith [Real.pi_pos]⟩) (sq_nonneg _)

/-- `sinθcos²θ` is strictly positive on the open quadrant `(0, π/2)`. -/
private theorem sinCos2_pos_of_mem {θ : ℝ} (h0 : 0 < θ) (h1 : θ < π / 2) :
    0 < Work.Elliptic.sinCos2 θ := by
  rw [Work.Elliptic.sinCos2]
  exact mul_pos (Real.sin_pos_of_mem_Ioo ⟨h0, by linarith [Real.pi_pos]⟩)
    (pow_pos (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h1⟩) 2)

/-- The integrand `rhoAux · sinθcos²θ` of the normalisation constant is continuous. -/
private theorem continuous_rhoAux_mul_sinCos2 :
    Continuous fun θ : ℝ => rhoAux θ * Work.Elliptic.sinCos2 θ := by
  simp only [rhoAux, cut01, Work.Elliptic.sinCos2]
  fun_prop

/-! ## The normalisation `∫_θ rho θ · sinθcos²θ = 1` -/

/-- The normalisation constant `crho = ∫_θ rhoAux θ · sinθcos²θ` is positive: the integrand
vanishes off `[1, 3/2]`, is nonnegative, and is strictly positive at `θ = 5/4`. -/
theorem crho_pos : 0 < crho := by
  have hone : 0 < ∫ θ in (0 : ℝ)..(π / 2), rhoAux θ * Work.Elliptic.sinCos2 θ := by
    refine intervalIntegral.integral_pos (by linarith [Real.pi_pos])
      continuous_rhoAux_mul_sinCos2.continuousOn
      (fun x hx => mul_nonneg (rhoAux_nonneg x)
        (sinCos2_nonneg_of_mem (le_of_lt hx.1) hx.2)) ?_
    refine ⟨5 / 4, ⟨by norm_num, by linarith [Real.pi_gt_three]⟩, ?_⟩
    exact mul_pos (rhoAux_pos_of_mem (by norm_num) (by norm_num))
      (sinCos2_pos_of_mem (by norm_num) (by linarith [Real.pi_gt_three]))
  rw [show crho = ∫ θ in (0 : ℝ)..(π / 2), rhoAux θ * Work.Elliptic.sinCos2 θ from ?_]
  exact hone
  rw [crho, Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]

/-- `crho ≠ 0`, so that the normalised profile `rho = crho⁻¹ * rhoAux` is nontrivial. -/
theorem crho_ne_zero : crho ≠ 0 := ne_of_gt crho_pos

/-- **The normalisation of the moment profile**: `∫_θ rho θ · sinθcos²θ = 1`. -/
theorem rho_moment : ∫ θ in Work.Spaces.Iθ, rho θ * Work.Elliptic.sinCos2 θ = 1 := by
  have h : ∫ θ in Work.Spaces.Iθ, rho θ * Work.Elliptic.sinCos2 θ
      = crho⁻¹ * ∫ θ in Work.Spaces.Iθ, rhoAux θ * Work.Elliptic.sinCos2 θ := by
    rw [show (fun θ : ℝ => rho θ * Work.Elliptic.sinCos2 θ)
        = fun θ : ℝ => crho⁻¹ * (rhoAux θ * Work.Elliptic.sinCos2 θ) from by
      funext θ
      simp only [rho]
      ring]
    rw [MeasureTheory.integral_const_mul]
  rw [h]
  show crho⁻¹ * crho = 1
  exact inv_mul_cancel₀ crho_ne_zero

/-! ## The angular moment of the approximation -/

theorem Fstar_approx {α : ℝ} {k : ℕ} {F : ℝ → ℝ → ℝ} (hF : Work.Spaces.HkMem α k F)
    (n : ℕ) (hn : 2 ≤ n) :
    ∀ z : ℝ, 0 < z →
      Work.Elliptic.Fstar (Work.FTS.PhiStar.Honesty.CptApp.approx n F) z = 0 := by
  -- neither `HkMem α k F` nor `2 ≤ n` is needed for this identity
  have _ := hF
  have _ := hn
  intro z hz
  -- the `rho`-piece of the integrand is always integrable (continuous with compact support)
  have hYint : MeasureTheory.Integrable
      (fun θ : ℝ => lam n F z * (rho θ * Work.Elliptic.sinCos2 θ))
      (volume.restrict Work.Spaces.Iθ) := by
    have h0 : MeasureTheory.IntegrableOn
        (fun θ : ℝ => rhoAux θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
      ContinuousOn.integrableOn_compact isCompact_Icc
        continuous_rhoAux_mul_sinCos2.continuousOn
    have h1 : MeasureTheory.Integrable
        (fun θ : ℝ => crho⁻¹ * (rhoAux θ * Work.Elliptic.sinCos2 θ))
        (volume.restrict Work.Spaces.Iθ) := h0.const_mul crho⁻¹
    have h2 : MeasureTheory.Integrable
        (fun θ : ℝ => rho θ * Work.Elliptic.sinCos2 θ)
        (volume.restrict Work.Spaces.Iθ) :=
      h1.congr (Filter.Eventually.of_forall (fun θ => by simp only [rho]; ring))
    exact h2.const_mul (lam n F z)
  -- the two integrals making up the moment
  have hXval : ∫ θ in Work.Spaces.Iθ, zetaR n θ * F z θ * Work.Elliptic.sinCos2 θ
      = lam n F z := rfl
  have hYval : ∫ θ in Work.Spaces.Iθ, lam n F z * (rho θ * Work.Elliptic.sinCos2 θ)
      = lam n F z := by
    rw [MeasureTheory.integral_const_mul, rho_moment, mul_one]
  -- the truncated moment integral vanishes
  have hmain : ∫ θ in Work.Spaces.Iθ,
      (zetaR n θ * F z θ - lam n F z * rho θ) * Work.Elliptic.sinCos2 θ = 0 := by
    rw [show (fun θ : ℝ => (zetaR n θ * F z θ - lam n F z * rho θ)
          * Work.Elliptic.sinCos2 θ)
        = (fun θ : ℝ => (zetaR n θ * F z θ * Work.Elliptic.sinCos2 θ)
            - (lam n F z * (rho θ * Work.Elliptic.sinCos2 θ))) from by
      funext θ
      ring]
    by_cases hX : MeasureTheory.Integrable
        (fun θ : ℝ => zetaR n θ * F z θ * Work.Elliptic.sinCos2 θ)
        (volume.restrict Work.Spaces.Iθ)
    · rw [MeasureTheory.integral_sub hX hYint, hXval, hYval]
      ring
    · -- `X` is not integrable: then `∫ X = 0` and `∫ (X - Y) = 0`, so the identity is trivial
      have hXY : ¬ MeasureTheory.Integrable
          (fun θ : ℝ => (zetaR n θ * F z θ * Work.Elliptic.sinCos2 θ)
            - (lam n F z * (rho θ * Work.Elliptic.sinCos2 θ)))
          (volume.restrict Work.Spaces.Iθ) := by
        intro h
        refine hX ((h.add hYint).congr (Filter.Eventually.of_forall (fun θ => ?_)))
        show (zetaR n θ * F z θ * Work.Elliptic.sinCos2 θ
            - lam n F z * (rho θ * Work.Elliptic.sinCos2 θ))
          + lam n F z * (rho θ * Work.Elliptic.sinCos2 θ)
          = zetaR n θ * F z θ * Work.Elliptic.sinCos2 θ
        ring
      rw [MeasureTheory.integral_undef hXY]
  rw [Work.Elliptic.Fstar]
  rw [show (fun θ : ℝ => approx n F z θ * Work.Elliptic.sinCos2 θ)
      = (fun θ : ℝ => chiR n z * ((zetaR n θ * F z θ - lam n F z * rho θ)
          * Work.Elliptic.sinCos2 θ)) from by
    funext θ
    simp only [approx]
    ring]
  rw [MeasureTheory.integral_const_mul, hmain, mul_zero]

end Work.FTS.PhiStar.Honesty.CptApp
