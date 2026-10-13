/-
Copyright: work module for the Elgindi finite-time singularity project.

# The sharp Bessel-type mode bound `eNorm m · (cmode m F z)² ≤ sliceMass`

`Work.FTS.PhiStar.Series.cmode m F z` is the `e_m`-coefficient of the slice `F z ·` in the
self-adjoint weight `cos θ dθ`, and `eNorm m = ∫_{Iθ} eFam m θ² cos θ` is the squared norm of
the mode.  This file proves the **sharp** (Cauchy–Schwarz in `L²`) bound

  `eNorm m * (cmode m F z)² ≤ ∫_{Iθ} (F z θ)² · sin(2θ)^{-η}`,

i.e. the `m`-th term of Bessel's inequality is dominated by the `η`-weighted slice mass (the
paper's angular weight `w_θ² = sin(2θ)^{-η}`).  This is the per-mode input of the honesty layer;
e.g. `Submission/Work/FTS/PhiStar/Honesty/integrableOn_acoeff_sq_w_sq_meas.lean` uses it to
dominate `cmode m F z²` by the slice mass, uniformly in `z`.

**Route.**  With the two halves of the weight,

  `A₀ θ = (F z θ)² · sin(2θ)^{-η}`,   `B₀ θ = (e_m θ · cos θ)² · sin(2θ)^{η}`,

Cauchy–Schwarz for `√A₀`, `√B₀` (the sibling lemma `sliceMass_moment_le`, proved from
`sq_integral_sqrt_mul_le`) gives

  `Aint² ≤ (∫_{Iθ} A₀) · (∫_{Iθ} B₀) = target · N`,

where `Aint = ∫_{Iθ} F z θ · e_m θ · cos θ` (`|Aint| ≤ ∫ |F z θ| |e_m θ cos θ|` by
`abs_integral_le_integral_abs`, and the two `rpow` halves of the weight multiply to `1` on the
interior of `Iθ`, the endpoints being null).  The second factor obeys the **sharp** bound

  `N = ∫_{Iθ} (e_m θ cos θ)² sin(2θ)^{η} ≤ ∫_{Iθ} e_m θ² cos θ = eNorm m`

(sibling lemma `eFam_cos_sq_sin_rpow_integral_le_eNorm`: on `Iθ` both `0 ≤ cos θ ≤ 1` and
`0 ≤ sin(2θ)^η ≤ 1`, hence `cos² θ · sin(2θ)^η ≤ cos θ`).  With
`cmode m F z = Aint / eNorm m` (`ModalSolution.cmode_eq`), `target ≥ 0` and `eNorm m > 0` this
is the claim.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.EllipticEst.ModalSolution.cmode_bessel
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.PhiStar.Honesty.eFam_cos_sq_sin_rpow_integral_le_eNorm
import Submission.Work.FTS.PhiStar.Honesty.sliceMass_moment_le

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

/-- `sin(2θ) ≥ 0` on `Iθ`. -/
private theorem sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- `cos θ ≥ 0` on `Iθ`. -/
private theorem cos_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.cos θ :=
  Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩

/-- **The sharp per-mode slice bound.**  For every `m` and every slice `F z ·` whose
`η`-weighted square is integrable on `Iθ`, the squared mode coefficient, weighted by the mode
norm `eNorm m`, is bounded by that weighted square:

  `eNorm m * (cmode m F z)² ≤ ∫_{Iθ} (F z θ)² sin(2θ)^{-η}`. -/
theorem eNorm_mul_cmode_sq_le_sliceMass {m : ℕ} {F : ℝ → ℝ → ℝ} {z : ℝ}
    (hint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ) :
    Work.EllipticEst.ModalSolution.eNorm m * (Work.FTS.PhiStar.Series.cmode m F z) ^ 2
      ≤ ∫ θ in Work.Spaces.Iθ,
          (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  set Aint : ℝ := ∫ θ in Work.Spaces.Iθ, F z θ * eF m θ * Real.cos θ with hAint
  set target : ℝ := ∫ θ in Work.Spaces.Iθ,
      (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) with htarget
  set N : ℝ := ∫ θ in Work.Spaces.Iθ,
      (eF m θ * Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (Work.Spaces.eta) with hN
  -- the slice mass is nonnegative (the integrand is a nonnegative a.e.-strongly-measurable
  -- function, as `hint` asserts integrability)
  have htnn : 0 ≤ target := by
    rw [htarget]
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _)
  -- the second Cauchy–Schwarz factor is dominated by the mode norm
  have hNle : N ≤ Work.EllipticEst.ModalSolution.eNorm m := by
    rw [hN]
    exact eFam_cos_sq_sin_rpow_integral_le_eNorm m
  -- the weighted Cauchy–Schwarz moment bound for the numerator
  have hmoment : Aint ^ 2 ≤ target * N := by
    rw [hAint, htarget, hN]
    exact sliceMass_moment_le (m := m) (F := F) (z := z) hint
  have hfin : Aint ^ 2 ≤ target * Work.EllipticEst.ModalSolution.eNorm m :=
    le_trans hmoment (mul_le_mul_of_nonneg_left hNle htnn)
  -- `cmode` is the numerator divided by the mode norm
  have hcm : Work.FTS.PhiStar.Series.cmode m F z
      = Aint / Work.EllipticEst.ModalSolution.eNorm m := by
    rw [Work.EllipticEst.ModalSolution.cmode_eq m F z]
    congr 1
    rw [hAint, Work.EllipticEst.ModalSolution.bInt]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
    have hc : 0 ≤ Real.cos θ := cos_nonneg_Iθ hθ
    conv_rhs => rw [← Real.sq_sqrt hc]
    ring
  have hE : 0 < Work.EllipticEst.ModalSolution.eNorm m :=
    Work.EllipticEst.ModalSolution.eNorm_pos m
  have hpow : (Work.EllipticEst.ModalSolution.eNorm m)
      * (Work.FTS.PhiStar.Series.cmode m F z) ^ 2
      = Aint ^ 2 / Work.EllipticEst.ModalSolution.eNorm m := by
    rw [hcm]
    field_simp
  calc Work.EllipticEst.ModalSolution.eNorm m * (Work.FTS.PhiStar.Series.cmode m F z) ^ 2
      = Aint ^ 2 / Work.EllipticEst.ModalSolution.eNorm m := hpow
    _ ≤ target * Work.EllipticEst.ModalSolution.eNorm m
          / Work.EllipticEst.ModalSolution.eNorm m :=
        div_le_div_of_nonneg_right hfin (le_of_lt hE)
    _ = target := by
        rw [mul_div_cancel_right₀ _ (ne_of_gt hE)]

end Work.FTS.PhiStar.Honesty
