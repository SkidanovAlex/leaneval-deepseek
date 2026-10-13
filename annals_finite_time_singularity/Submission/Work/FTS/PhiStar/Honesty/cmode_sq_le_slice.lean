/-
Copyright: work module for the Elgindi finite-time singularity project.

# The slice bound on the mode coefficients `cmode`

`Work.FTS.PhiStar.Series.cmode m F z` is the `e_m`-coefficient of the slice `F z ·` in the
self-adjoint weight `cos θ dθ`,

  `cmode m F z = (∫_{0}^{π/2} F z θ · e_m θ · cos θ) / (∫_{0}^{π/2} e_m θ² · cos θ)`,

and this file bounds it by the *weighted `L²`-norm of the slice* with the paper's weight
`sin(2θ)^{-η}` (this is the per-mode input of the honesty layer, see
`NOTES_honesty_seed.md` §3):

  `(cmode m F z)² ≤ C_m · ∫_{Iθ} (F z θ)² · sin(2θ)^{-η}`,

with a constant `C_m` depending only on `m`.

**Route.**  The denominator is explicit, `cmdD m = ((2m+2)(2m+3))/(4m+5) > 0`
(`Gegenbauer.FamNormValue`), so it is enough to bound the numerator
`A = ∫_{Iθ} F z θ · e_m θ · cos θ` squared.  Cauchy–Schwarz for the two functions
`√A₀`, `√B₀` with

  `A₀ θ = (F z θ)² · sin(2θ)^{-η}`,   `B₀ θ = (e_m θ · cos θ)² · sin(2θ)^{η}`

gives `(∫_{Iθ} √A₀ √B₀)² ≤ (∫ A₀)(∫ B₀) = target · N_m`, and on the interior of `Iθ`
(where `sin(2θ) > 0`, so the `rpow` identities apply) the left-hand side is
`(∫_{Iθ} |F z θ| · |e_m θ cos θ|)² ≥ A²`.  The two endpoints `0, π/2`, where `sin(2θ) = 0`
and the `rpow` values are junk, are null for `volume.restrict Iθ`.  Finally
`N_m ≤ N_m + 1` and `target ≥ 0` give the stated shape with `C_m = (N_m + 1)/cmdD m²`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.FamNormValue
import Submission.Work.Spaces.cs_integral
import Submission.Work.PhiStar.Honesty.sq_integral_sqrt_mul_le
import Submission.Work.PhiStar.Honesty.integrableOn_eFam_cos_sq_sin_rpow
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory
open scoped Real

namespace Work.FTS.PhiStar.Honesty

set_option autoImplicit false

/-- The `m`-th Gegenbauer mode `e_m`, locally abbreviated. -/
private abbrev eF (m : ℕ) : ℝ → ℝ := Work.FTS.PhiStar.Gegenbauer.eFam m

/-- Almost every point of `Iθ = [0, π/2]` is interior: the two endpoints are null. -/
private theorem ae_mem_Ioo_Iθ :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo (0 : ℝ) (π / 2) := by
  have h : volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) :=
    Measure.restrict_congr_set (MeasureTheory.Ioo_ae_eq_Icc (μ := volume)).symm
  rw [h]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-- The set integral over `Iθ = [0, π/2]` is the interval integral over `0..π/2`. -/
private theorem setIntegral_Iθ_eq_intervalIntegral (g : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, g θ) = ∫ θ in (0 : ℝ)..(Real.pi / 2), g θ := by
  rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2)]

/-- `sin(2θ) ≥ 0` on `Iθ`. -/
private theorem sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- **The per-mode slice bound.**  For every `m`, slice `F z ·` whose `η`-weighted square is
integrable, `(cmode m F z)²` is bounded by that weighted square with a constant depending only
on `m`. -/
theorem cmode_sq_le_slice (m : ℕ) (F : ℝ → ℝ → ℝ) (z : ℝ)
    (hint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ) :
    ∃ C : ℝ, 0 < C ∧ (Work.FTS.PhiStar.Series.cmode m F z) ^ 2
      ≤ C * ∫ θ in Work.Spaces.Iθ,
        (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  -- the numerator, the denominator, the Cauchy–Schwarz constant and the target integral
  set Aint : ℝ := ∫ θ in (0 : ℝ)..(Real.pi / 2), F z θ * eF m θ * Real.cos θ with hAint
  set Bden : ℝ := ∫ θ in (0 : ℝ)..(Real.pi / 2), eF m θ ^ 2 * Real.cos θ with hBden
  set N : ℝ := ∫ θ in Work.Spaces.Iθ,
      (eF m θ * Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (Work.Spaces.eta) with hN
  set target : ℝ := ∫ θ in Work.Spaces.Iθ,
      (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) with htarget
  -- the explicit value of the denominator
  have hBpos : 0 < Bden := by
    rw [hBden, Work.FTS.PhiStar.Gegenbauer.FamNormValue m]
    positivity
  have hNnn : 0 ≤ N := by
    have := (Work.PhiStar.Honesty.integrableOn_eFam_cos_sq_sin_rpow m).2
    rwa [hN]
  have htnn : 0 ≤ target := by
    rw [htarget]
    refine integral_nonneg_of_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem (μ := volume) (s := Work.Spaces.Iθ)
      measurableSet_Icc] with θ hθ
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _)
  refine ⟨(N + 1) / Bden ^ 2, div_pos (by linarith) (pow_pos hBpos 2), ?_⟩
  -- `cmode` is the numerator divided by the denominator
  have hcm : Work.FTS.PhiStar.Series.cmode m F z = Aint / Bden := by
    rw [Work.FTS.PhiStar.Series.cmode, hAint, hBden]
  rw [hcm]
  -- the moment bound `Aint² ≤ target · N`
  have hmoment : Aint ^ 2 ≤ target * N := by
    -- the numerator, as a set integral over `Iθ`
    have hK : |Aint| ≤ ∫ θ in Work.Spaces.Iθ, |F z θ| * |eF m θ * Real.cos θ| := by
      rw [hAint, ← setIntegral_Iθ_eq_intervalIntegral
        (fun θ => F z θ * eF m θ * Real.cos θ)]
      refine (MeasureTheory.abs_integral_le_integral_abs
        (μ := volume.restrict Work.Spaces.Iθ)
        (f := fun θ => F z θ * eF m θ * Real.cos θ)).trans ?_
      refine le_of_eq (setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_)
      simp only [abs_mul]
      ring
    have hAnn : ∀ θ ∈ Work.Spaces.Iθ,
        0 ≤ (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
      fun θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _)
    have hBnn : ∀ θ ∈ Work.Spaces.Iθ,
        0 ≤ (eF m θ * Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (Work.Spaces.eta) :=
      fun θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _)
    -- Cauchy–Schwarz on the two halves of the weight
    have hcs := Work.PhiStar.Honesty.sq_integral_sqrt_mul_le (s := Work.Spaces.Iθ)
      measurableSet_Icc
      (A := fun θ => (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (B := fun θ => (eF m θ * Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (Work.Spaces.eta))
      hint (Work.PhiStar.Honesty.integrableOn_eFam_cos_sq_sin_rpow m).1 hAnn hBnn
    -- on the interior the square-root product is `|F z θ| · |e_m θ cos θ|`
    have hae : (fun θ => Real.sqrt ((F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          * Real.sqrt ((eF m θ * Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (Work.Spaces.eta)))
        =ᵐ[volume.restrict Work.Spaces.Iθ] (fun θ => |F z θ| * |eF m θ * Real.cos θ|) := by
      filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
      exact Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo F m z hθ
    have hcs' : (∫ θ in Work.Spaces.Iθ, |F z θ| * |eF m θ * Real.cos θ|) ^ 2
        ≤ target * N := by
      rw [← integral_congr_ae hae]
      exact hcs
    have h1 := pow_le_pow_left₀ (abs_nonneg Aint) hK 2
    calc Aint ^ 2 = |Aint| ^ 2 := (sq_abs Aint).symm
      _ ≤ (∫ θ in Work.Spaces.Iθ, |F z θ| * |eF m θ * Real.cos θ|) ^ 2 := h1
      _ ≤ target * N := hcs'
  -- the arithmetic
  have hfin : Aint ^ 2 ≤ (N + 1) * target := by
    calc Aint ^ 2 ≤ target * N := hmoment
      _ ≤ target * (N + 1) := mul_le_mul_of_nonneg_left (by linarith) htnn
      _ = (N + 1) * target := by ring
  have hB2 : 0 < Bden ^ 2 := pow_pos hBpos 2
  calc (Aint / Bden) ^ 2 = Aint ^ 2 / Bden ^ 2 := by rw [div_pow]
    _ ≤ ((N + 1) * target) / Bden ^ 2 := div_le_div_of_nonneg_right hfin (le_of_lt hB2)
    _ = ((N + 1) / Bden ^ 2) * target := by ring

end Work.FTS.PhiStar.Honesty
