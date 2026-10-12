import ChallengeDeps
import Mathlib.Analysis.Fourier.Notation
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.BoseFixR.mass_le_W1omega
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR

open MeasureTheory
open scoped ENNReal Topology Real FourierTransform

set_option autoImplicit false
set_option maxHeartbeats 1600000

open Submission.BoseGases

/-- `c * a ≤ c * b` in `ℝ≥0∞` from `a ≤ b`. -/
private lemma mul_le_mul_left_ennreal' {a b c : ℝ≥0∞} (h : a ≤ b) : c * a ≤ c * b :=
  mul_le_mul_of_nonneg_left h (zero_le : (0 : ℝ≥0∞) ≤ c)

theorem mass_le_W1omega2 {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) {R ℓ : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) (hℓ : 0 < ℓ)
    (hW : MeasureTheory.Integrable (Work.BoseFixR.W1fun v h ℓ)) :
    ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : EuclideanSpace ℝ (Fin 3),
        (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) q) ^ 2 / (2 * ‖q‖ ^ 2)
      ≤ 2 * ∫ x : EuclideanSpace ℝ (Fin 3), Work.BoseFixR.W1omegaFun v h ℓ x := by
  change ((2 * Real.pi) ^ 3)⁻¹ * (∫ q : ℝ³, (chat (wScaled ℓ (g0 v h)) q) ^ 2 / (2 * ‖q‖ ^ 2))
      ≤ 2 * (∫ x : ℝ³, W1omegaFun v h ℓ x)
  -- the a.e. positivity facts
  have hWnn : ∀ᵐ x : ℝ³, 0 ≤ wScaled ℓ (g0 v h) x :=
    wScaled_g0_nonneg_ae (v := v) (R := R) hR hv hvrad hv_supp h
  have hw0nn : ∀ᵐ x : ℝ³, 0 ≤ Classical.choose h x :=
    (chosen_w0_bounds_ae (v := v) (R := R) hR hv hvrad hv_supp h).1
  have hWi : Integrable (wScaled ℓ (g0 v h)) := hW
  -- the mass is nonnegative
  have hMnn : 0 ≤ ∫ x : ℝ³, wScaled ℓ (g0 v h) x * Classical.choose h x := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [hWnn, hw0nn] with x hx hw
    exact mul_nonneg hx hw
  -- the three external inputs
  have hfour := fourier_coulomb_le (wScaled ℓ (g0 v h)) hWi hWnn
  have hPA := lintegral_W1W1_le_two_W1g0 (v := v) h (R := R) (ℓ := ℓ) hR hv hvrad hv_supp hRℓ hℓ
  have hPB := lintegral_W1_g0_eq (v := v) h (R := R) (ℓ := ℓ) hR hv hvrad hv_supp hRℓ hℓ
  -- the ENNReal chain
  have hhalf2 : (1 / 2 : ℝ≥0∞) * 2 = 1 := by
    have h := ENNReal.inv_mul_cancel (a := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
    simpa using h
  have hMnn' : 0 ≤ ∫ x : ℝ³, W1omegaFun v h ℓ x := by
    rw [mass_eq v h ℓ]
    exact hMnn
  have hpi8 : (1 / (4 * Real.pi)) * (8 * Real.pi) = 2 := by
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
    norm_num
  have key : ENNReal.ofReal (((2 * Real.pi) ^ 3)⁻¹)
        * (∫⁻ q : ℝ³, ENNReal.ofReal ((chat (wScaled ℓ (g0 v h)) q) ^ 2 / (2 * ‖q‖ ^ 2)))
      ≤ ENNReal.ofReal (2 * ∫ x : ℝ³, W1omegaFun v h ℓ x) := by
    have hstep1 := lintegral_chat_le_kinFT (wScaled ℓ (g0 v h))
    calc ENNReal.ofReal (((2 * Real.pi) ^ 3)⁻¹)
          * (∫⁻ q : ℝ³, ENNReal.ofReal ((chat (wScaled ℓ (g0 v h)) q) ^ 2 / (2 * ‖q‖ ^ 2)))
        ≤ ENNReal.ofReal (((2 * Real.pi) ^ 3)⁻¹)
            * ((1 / 2 : ℝ≥0∞) * (∫⁻ q : ℝ³, ENNReal.ofReal
                (‖kinFT (fun y : ℝ³ => ((wScaled ℓ (g0 v h) y : ℝ) : ℂ)) q‖ ^ 2
                  / ‖q‖ ^ 2))) :=
          mul_le_mul_left_ennreal' hstep1
        _ = (1 / 2 : ℝ≥0∞) * (ENNReal.ofReal (((2 * Real.pi) ^ 3)⁻¹)
            * (∫⁻ q : ℝ³, ENNReal.ofReal
                (‖kinFT (fun y : ℝ³ => ((wScaled ℓ (g0 v h) y : ℝ) : ℂ)) q‖ ^ 2
                  / ‖q‖ ^ 2))) := by ring
        _ ≤ (1 / 2 : ℝ≥0∞) * (ENNReal.ofReal (1 / (4 * Real.pi))
            * (∫⁻ x : ℝ³, ∫⁻ y : ℝ³, ENNReal.ofReal
                (wScaled ℓ (g0 v h) x * wScaled ℓ (g0 v h) y / ‖x - y‖))) :=
          mul_le_mul_left_ennreal' hfour
        _ ≤ (1 / 2 : ℝ≥0∞) * (ENNReal.ofReal (1 / (4 * Real.pi))
            * (2 * (∫⁻ x : ℝ³, ∫⁻ y : ℝ³, ENNReal.ofReal
                (wScaled ℓ (g0 v h) x * g0 v h y / ‖x - y‖)))) :=
          mul_le_mul_left_ennreal' (mul_le_mul_left_ennreal' hPA)
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
  -- take `.toReal` on both sides
  have hI : (∫ q : ℝ³, (chat (wScaled ℓ (g0 v h)) q) ^ 2 / (2 * ‖q‖ ^ 2))
      = (∫⁻ q : ℝ³,
          ENNReal.ofReal ((chat (wScaled ℓ (g0 v h)) q) ^ 2 / (2 * ‖q‖ ^ 2))).toReal := by
    refine integral_eq_lintegral_of_nonneg_ae ?_ ?_
    · filter_upwards with q
      exact div_nonneg (sq_nonneg _) (by positivity)
    · have h1 : AEMeasurable (fun q : ℝ³ => (chat (wScaled ℓ (g0 v h)) q) ^ 2) volume :=
        (AEStronglyMeasurable.pow (aestronglyMeasurable_chat (wScaled ℓ (g0 v h)) hWi) 2).aemeasurable
      have h2 : AEMeasurable (fun q : ℝ³ => 2 * ‖q‖ ^ 2) volume :=
        (continuous_const.mul (continuous_norm.pow 2)).aemeasurable
      exact (h1.div h2).aestronglyMeasurable
  calc ((2 * Real.pi) ^ 3)⁻¹
        * (∫ q : ℝ³, (chat (wScaled ℓ (g0 v h)) q) ^ 2 / (2 * ‖q‖ ^ 2))
      = (ENNReal.ofReal (((2 * Real.pi) ^ 3)⁻¹)
          * (∫⁻ q : ℝ³,
              ENNReal.ofReal ((chat (wScaled ℓ (g0 v h)) q) ^ 2 / (2 * ‖q‖ ^ 2)))).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), hI]
    _ ≤ (ENNReal.ofReal (2 * ∫ x : ℝ³, W1omegaFun v h ℓ x)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top key
    _ = 2 * ∫ x : ℝ³, W1omegaFun v h ℓ x :=
        ENNReal.toReal_ofReal (by linarith [hMnn'])

end Work.BoseFixR
