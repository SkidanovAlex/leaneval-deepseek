import ChallengeDeps
import Submission.Work.BoseFixR.ChiR0Defs
import Submission.Work.BoseFixR.mass_le_W1omega2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory
open scoped ENNReal Topology Real
open Submission.BoseGases

namespace Work.BoseFixR

theorem IntegrableChatW1sq {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hvrad : BoseGases.IsRadial v) {R ℓ : ℝ} (hR : 0 < R) (hℓ : 0 < ℓ)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) :
    MeasureTheory.Integrable (fun q : EuclideanSpace ℝ (Fin 3) =>
      (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) q) ^ 2 / (2 * ‖q‖ ^ 2)) := by
  change MeasureTheory.Integrable (fun q : ℝ³ =>
      (chat (wScaled ℓ (g0 v h)) q) ^ 2 / (2 * ‖q‖ ^ 2))
  have hW : Integrable (wScaled ℓ (g0 v h)) := wScaled_g0_integrable hR hv_supp h hℓ hRℓ
  have hWnn : ∀ᵐ x : ℝ³, 0 ≤ wScaled ℓ (g0 v h) x :=
    wScaled_g0_nonneg_ae (v := v) (R := R) hR hv hvrad hv_supp h
  have hstep1 := lintegral_chat_le_kinFT (wScaled ℓ (g0 v h))
  have hfour := fourier_coulomb_le (wScaled ℓ (g0 v h)) hW hWnn
  have hPA := lintegral_W1W1_le_two_W1g0 (v := v) h (R := R) (ℓ := ℓ) hR hv hvrad hv_supp hRℓ hℓ
  have hPB := lintegral_W1_g0_eq (v := v) h (R := R) (ℓ := ℓ) hR hv hvrad hv_supp hRℓ hℓ
  have hhalf2 : (1 / 2 : ℝ≥0∞) * 2 = 1 := by
    have h := ENNReal.inv_mul_cancel (a := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
    simpa using h
  have hpi8 : (1 / (4 * Real.pi)) * (8 * Real.pi) = 2 := by
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
    norm_num
  have key : ENNReal.ofReal (((2 * Real.pi) ^ 3)⁻¹)
        * (∫⁻ q : ℝ³, ENNReal.ofReal ((chat (wScaled ℓ (g0 v h)) q) ^ 2 / (2 * ‖q‖ ^ 2)))
      ≤ ENNReal.ofReal (2 * ∫ x : ℝ³, W1omegaFun v h ℓ x) := by
    calc ENNReal.ofReal (((2 * Real.pi) ^ 3)⁻¹)
          * (∫⁻ q : ℝ³, ENNReal.ofReal ((chat (wScaled ℓ (g0 v h)) q) ^ 2 / (2 * ‖q‖ ^ 2)))
        ≤ ENNReal.ofReal (((2 * Real.pi) ^ 3)⁻¹)
            * ((1 / 2 : ℝ≥0∞) * (∫⁻ q : ℝ³, ENNReal.ofReal
                (‖kinFT (fun y : ℝ³ => ((wScaled ℓ (g0 v h) y : ℝ) : ℂ)) q‖ ^ 2
                  / ‖q‖ ^ 2))) :=
          mul_le_mul_of_nonneg_left hstep1 zero_le
        _ = (1 / 2 : ℝ≥0∞) * (ENNReal.ofReal (((2 * Real.pi) ^ 3)⁻¹)
            * (∫⁻ q : ℝ³, ENNReal.ofReal
                (‖kinFT (fun y : ℝ³ => ((wScaled ℓ (g0 v h) y : ℝ) : ℂ)) q‖ ^ 2
                  / ‖q‖ ^ 2))) := by ring
        _ ≤ (1 / 2 : ℝ≥0∞) * (ENNReal.ofReal (1 / (4 * Real.pi))
            * (∫⁻ x : ℝ³, ∫⁻ y : ℝ³, ENNReal.ofReal
                (wScaled ℓ (g0 v h) x * wScaled ℓ (g0 v h) y / ‖x - y‖))) :=
          mul_le_mul_of_nonneg_left hfour zero_le
        _ ≤ (1 / 2 : ℝ≥0∞) * (ENNReal.ofReal (1 / (4 * Real.pi))
            * (2 * (∫⁻ x : ℝ³, ∫⁻ y : ℝ³, ENNReal.ofReal
                (wScaled ℓ (g0 v h) x * g0 v h y / ‖x - y‖)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hPA zero_le) zero_le
        _ = (1 / 2 : ℝ≥0∞) * (ENNReal.ofReal (1 / (4 * Real.pi))
            * (2 * (ENNReal.ofReal (8 * Real.pi)
                * ENNReal.ofReal (∫ x : ℝ³,
                    wScaled ℓ (g0 v h) x * Classical.choose h x)))) := by
          rw [hPB]
        _ = ENNReal.ofReal (1 / (4 * Real.pi)) * ENNReal.ofReal (8 * Real.pi)
            * ENNReal.ofReal (∫ x : ℝ³,
                wScaled ℓ (g0 v h) x * Classical.choose h x) := by
          rw [show (1 / 2 : ℝ≥0∞) * (ENNReal.ofReal (1 / (4 * Real.pi))
              * (2 * (ENNReal.ofReal (8 * Real.pi)
                * ENNReal.ofReal (∫ x : ℝ³,
                    wScaled ℓ (g0 v h) x * Classical.choose h x))))
            = ((1 / 2 : ℝ≥0∞) * 2) * (ENNReal.ofReal (1 / (4 * Real.pi))
              * (ENNReal.ofReal (8 * Real.pi)
                * ENNReal.ofReal (∫ x : ℝ³,
                    wScaled ℓ (g0 v h) x * Classical.choose h x))) from by ring,
            hhalf2, one_mul, mul_assoc]
        _ = ENNReal.ofReal ((1 / (4 * Real.pi)) * (8 * Real.pi))
            * ENNReal.ofReal (∫ x : ℝ³,
                wScaled ℓ (g0 v h) x * Classical.choose h x) := by
          rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 / (4 * Real.pi))]
        _ = ENNReal.ofReal 2 * ENNReal.ofReal (∫ x : ℝ³,
                wScaled ℓ (g0 v h) x * Classical.choose h x) := by rw [hpi8]
        _ = ENNReal.ofReal (2 * ∫ x : ℝ³,
                wScaled ℓ (g0 v h) x * Classical.choose h x) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        _ = ENNReal.ofReal (2 * ∫ x : ℝ³, W1omegaFun v h ℓ x) := by
          congr 1
          congr 1
          exact (mass_eq v h ℓ).symm
  refine ⟨?_, ?_⟩
  · exact (((continuous_chat (wScaled ℓ (g0 v h)) hW).measurable.pow_const 2).div
      ((continuous_const.mul (continuous_norm.pow 2)).measurable)).aestronglyMeasurable
  · rw [hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall (fun q : ℝ³ => by positivity))]
    -- `ofReal((2π)³⁻¹) * X ≤ ofReal C` with `ofReal((2π)³⁻¹) ≠ 0` forces `X < ∞`
    have hc0 : ENNReal.ofReal (((2 * Real.pi) ^ 3)⁻¹) ≠ 0 :=
      ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
    have hprod : ENNReal.ofReal (((2 * Real.pi) ^ 3)⁻¹)
        * (∫⁻ q : ℝ³,
            ENNReal.ofReal ((chat (wScaled ℓ (g0 v h)) q) ^ 2 / (2 * ‖q‖ ^ 2))) < ⊤ :=
      lt_of_le_of_lt key ENNReal.ofReal_lt_top
    rcases ENNReal.mul_lt_top_iff.mp hprod with ⟨-, hx⟩ | ha0 | hb0
    · exact hx
    · exact absurd ha0 hc0
    · rw [hb0]
      exact ENNReal.zero_lt_top

end Work.BoseFixR
