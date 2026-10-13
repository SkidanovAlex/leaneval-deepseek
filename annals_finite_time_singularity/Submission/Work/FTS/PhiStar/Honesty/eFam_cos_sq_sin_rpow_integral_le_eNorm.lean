/-
# `eFam_cos_sq_sin_rpow_integral_le_eNorm`

The `η`-weighted `L²`-mass of the mode `eFam m · cos` is dominated by the *unweighted*
`L²(Iθ, cos θ dθ)`-norm square `eNorm m` of the mode.

On `Iθ = [0, π/2]` we have `0 ≤ sin (2θ) ≤ 1`, `0 ≤ cos θ ≤ 1` and `η = 99/100 > 0`, so
pointwise

  `(eFam m θ · cos θ)² · sin(2θ)^η ≤ (eFam m θ · cos θ)² · 1 = eFam m θ² · cos²θ ≤ eFam m θ² · cos θ`,

and `eNorm m` is by definition `∫ θ in Iθ, eFam m θ² · cos θ`.  Both integrands are
continuous on the compact `Iθ`, so `setIntegral_mono_on` applies.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.EllipticEst.ModalSolution.cmode_bessel
import Submission.Work.FTS.PhiStar.Gegenbauer.FamNormValue

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open MeasureTheory
open scoped Real

namespace Work.FTS.PhiStar.Honesty

/-- `sin (2θ) ≥ 0` for `θ ∈ Iθ = [0, π/2]`. -/
private lemma sin_two_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- `cos θ ≥ 0` for `θ ∈ Iθ = [0, π/2]`. -/
private lemma cos_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.cos θ :=
  Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩

/-- `θ ↦ sin (2θ)^η` is continuous on `Iθ` (`η` is the nonzero constant `99/100`). -/
private lemma continuousOn_sin_two_rpow_eta :
    ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (Work.Spaces.eta)) Work.Spaces.Iθ :=
  ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
    (fun _ _ => Or.inr (by norm_num [Work.Spaces.eta]))

theorem eFam_cos_sq_sin_rpow_integral_le_eNorm (m : ℕ) :
    (∫ θ in Work.Spaces.Iθ,
        (Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) ^ 2
          * (Real.sin (2 * θ)) ^ (Work.Spaces.eta))
      ≤ Work.EllipticEst.ModalSolution.eNorm m := by
  rw [Work.EllipticEst.ModalSolution.eNorm]
  have hI : MeasurableSet Work.Spaces.Iθ := Work.EllipticEst.ModalSolution.measurableSet_Iθ
  -- integrability of the two integrands on the compact `Iθ`
  have hcontL : ContinuousOn
      (fun θ : ℝ => (Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) ^ 2
        * (Real.sin (2 * θ)) ^ (Work.Spaces.eta)) Work.Spaces.Iθ :=
    (((Work.EllipticEst.ModalSolution.continuous_eFam m).mul
      Real.continuous_cos).pow 2).continuousOn.mul continuousOn_sin_two_rpow_eta
  have hcontR : Continuous
      (fun θ : ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ) :=
    ((Work.EllipticEst.ModalSolution.continuous_eFam m).pow 2).mul Real.continuous_cos
  refine MeasureTheory.setIntegral_mono_on
    (hcontL.integrableOn_compact isCompact_Icc)
    (hcontR.continuousOn.integrableOn_compact isCompact_Icc) hI ?_
  intro θ hθ
  have hcos0 : 0 ≤ Real.cos θ := cos_nonneg_of_mem_Iθ hθ
  have hcos1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hrpow : (Real.sin (2 * θ)) ^ (Work.Spaces.eta) ≤ 1 :=
    Real.rpow_le_one hs0 hs1 Work.Spaces.eta_nonneg
  have hc2 : Real.cos θ ^ 2 ≤ Real.cos θ := by nlinarith
  have hsq : (Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) ^ 2
      = Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ ^ 2 := by ring
  calc (Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) ^ 2
        * (Real.sin (2 * θ)) ^ (Work.Spaces.eta)
      ≤ (Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hrpow (sq_nonneg _)
    _ = (Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) ^ 2 := mul_one _
    _ = Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ ^ 2 := hsq
    _ ≤ Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ :=
        mul_le_mul_of_nonneg_left hc2 (sq_nonneg _)

end Work.FTS.PhiStar.Honesty
