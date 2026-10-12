import ChallengeDeps
import Mathlib.Analysis.Fourier.Notation
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.BoseFixR.mass_le_W1omega2
import Submission.Work.BoseFixR.sampling_sq_sum_le
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

-- (`ℝ³` is the corpus's *global* notation of `Submission.Work.BoseKinLoc/Defs.lean`, in the import
-- cone; do not redeclare it locally.)

/-- `c * a ≤ c * b` in `ℝ≥0∞` from `a ≤ b`. -/
private lemma mul_le_mul_left_ennrealS {a b c : ℝ≥0∞} (h : a ≤ b) : c * a ≤ c * b :=
  mul_le_mul_of_nonneg_left h (zero_le : (0 : ℝ≥0∞) ≤ c)

/-! ## 1. The quantitative sandwich `W₁ ≤ (1 + S(R/ℓ)²)·g₀` -/

/-- **The quantitative sandwich.**  In the dilute regime `R ≤ ℓ·chiR0`, on the support of `g₀`
(which is contained in `ball 0 R`, and where `χ⋆χ ≥ 1/2`), the hypothesis `hconv` on the Taylor
remainder of `χ⋆χ` gives `1/(χ⋆χ) ≤ 1 + S(‖y‖/ℓ)²`, whence

    `W₁ y = g₀(y)/(χ⋆χ)(y) ≤ (1 + S(R/ℓ)²)·g₀(y)`  for a.e. `y`.

This is the quantitative replacement of `wScaled_abs_le_two` (`W₁ ≤ 2g₀`) in the mass comparison;
the factor is legitimate because `g₀` vanishes outside `ball 0 R`, so the a.e. inequality
`‖y‖ ≤ R` needed for `hconv` is automatic where `g₀ ≠ 0` (and `g₀ ≥ 0` a.e. by `g0_nonneg_ae`). -/
lemma wScaled_le_oneAddS_g0 {v : ℝ³ → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hvrad : BoseGases.IsRadial v) {R ℓ S : ℝ} (hR : 0 < R) (hℓ : 0 < ℓ)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hRℓ : R ≤ ℓ * chiR0) (hS : 0 ≤ S)
    (hconv : ∀ x : ℝ³, ‖x‖ ≤ R →
        (1 - convScale ℓ x) / convScale ℓ x ≤ S * (‖x‖ / ℓ) ^ 2) :
    ∀ᵐ y : ℝ³, wScaled ℓ (g0 v h) y ≤ (1 + S * (R / ℓ) ^ 2) * g0 v h y := by
  have hgnn : ∀ᵐ x : ℝ³, 0 ≤ g0 v h x := g0_nonneg_ae hR hv hvrad hv_supp h
  filter_upwards [hgnn] with y hy
  by_cases h0 : g0 v h y = 0
  · have hz : wScaled ℓ (g0 v h) y = 0 := by simp [wScaled, h0]
    rw [hz, h0, mul_zero]
  · -- then `y` lies strictly inside the ball of radius `R`
    have hlt : ‖y‖ < R := lt_of_not_ge fun hle => h0 (g0_zero_of_norm_ge hv_supp hle h)
    have h0pos : 0 < g0 v h y := lt_of_le_of_ne hy (Ne.symm h0)
    -- `χ⋆χ ≥ 1/2 > 0` at `y`
    have hc : 0 < convScale ℓ y :=
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2)
        (convScale_ge_half_ball hℓ hR.le hRℓ (le_of_lt hlt))
    -- `hconv` rearranged: `1/(χ⋆χ) ≤ 1 + S(‖y‖/ℓ)²`
    have hkey : (convScale ℓ y)⁻¹ ≤ 1 + S * (‖y‖ / ℓ) ^ 2 := by
      have h2 : 1 - convScale ℓ y ≤ S * (‖y‖ / ℓ) ^ 2 * convScale ℓ y :=
        (div_le_iff₀ hc).mp (hconv y (le_of_lt hlt))
      calc (convScale ℓ y)⁻¹ = 1 / convScale ℓ y := inv_eq_one_div _
        _ ≤ 1 + S * (‖y‖ / ℓ) ^ 2 := by
            rw [div_le_iff₀ hc]
            calc (1 : ℝ) = 1 - convScale ℓ y + convScale ℓ y := by ring
              _ ≤ S * (‖y‖ / ℓ) ^ 2 * convScale ℓ y + convScale ℓ y := by linarith
              _ = (1 + S * (‖y‖ / ℓ) ^ 2) * convScale ℓ y := by ring
    -- and `1 + S(‖y‖/ℓ)² ≤ 1 + S(R/ℓ)²` because `‖y‖ ≤ R`
    have hCR : 1 + S * (‖y‖ / ℓ) ^ 2 ≤ 1 + S * (R / ℓ) ^ 2 := by
      have h1 : ‖y‖ / ℓ ≤ R / ℓ := by
        rw [div_le_div_iff_of_pos_right hℓ]
        exact le_of_lt hlt
      have h2 : (‖y‖ / ℓ) ^ 2 ≤ (R / ℓ) ^ 2 :=
        pow_le_pow_left₀ (div_nonneg (norm_nonneg _) hℓ.le) h1 2
      linarith [mul_le_mul_of_nonneg_left h2 hS]
    calc wScaled ℓ (g0 v h) y = g0 v h y * (convScale ℓ y)⁻¹ := by
          rw [wScaled, div_eq_mul_inv]
      _ ≤ g0 v h y * (1 + S * (‖y‖ / ℓ) ^ 2) :=
          mul_le_mul_of_nonneg_left hkey (le_of_lt h0pos)
      _ ≤ g0 v h y * (1 + S * (R / ℓ) ^ 2) :=
          mul_le_mul_of_nonneg_left hCR (le_of_lt h0pos)
      _ = (1 + S * (R / ℓ) ^ 2) * g0 v h y := by ring

/-! ## 2. The quantitative `W₁⊗W₁` versus `W₁⊗g₀` Coulomb comparison -/

/-- The quantitative form of `Work.BoseFixR.lintegral_W1W1_le_two_W1g0`: the factor `2` of the
crude sandwich `W₁ ≤ 2g₀` is replaced by `1 + S(R/ℓ)²` via `wScaled_le_oneAddS_g0`. -/
theorem lintegral_W1W1_le_oneAddS_W1g0 {v : ℝ³ → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hvrad : BoseGases.IsRadial v) {R ℓ S : ℝ} (hR : 0 < R) (hℓ : 0 < ℓ)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hRℓ : R ≤ ℓ * chiR0) (hS : 0 ≤ S)
    (hconv : ∀ x : ℝ³, ‖x‖ ≤ R →
        (1 - convScale ℓ x) / convScale ℓ x ≤ S * (‖x‖ / ℓ) ^ 2) :
    (∫⁻ x : ℝ³, ∫⁻ y : ℝ³,
        ENNReal.ofReal (wScaled ℓ (g0 v h) x * wScaled ℓ (g0 v h) y / ‖x - y‖))
      ≤ ENNReal.ofReal (1 + S * (R / ℓ) ^ 2)
        * ∫⁻ x : ℝ³, ∫⁻ y : ℝ³,
            ENNReal.ofReal (wScaled ℓ (g0 v h) x * g0 v h y / ‖x - y‖) := by
  have hCnn : 0 ≤ 1 + S * (R / ℓ) ^ 2 := by
    have := mul_nonneg hS (sq_nonneg (R / ℓ))
    linarith
  -- the a.e. quantitative sandwich
  have hWy := wScaled_le_oneAddS_g0 (v := v) h hv hvrad hR hℓ hv_supp hRℓ hS hconv
  -- the inner comparison, for every `x` with `0 ≤ W₁ x`
  have hinner : ∀ x : ℝ³, 0 ≤ wScaled ℓ (g0 v h) x →
      (∫⁻ y : ℝ³,
          ENNReal.ofReal (wScaled ℓ (g0 v h) x * wScaled ℓ (g0 v h) y / ‖x - y‖))
        ≤ ENNReal.ofReal (1 + S * (R / ℓ) ^ 2) * (∫⁻ y : ℝ³, ENNReal.ofReal
            (wScaled ℓ (g0 v h) x * g0 v h y / ‖x - y‖)) := by
    intro x hx
    calc (∫⁻ y : ℝ³,
            ENNReal.ofReal (wScaled ℓ (g0 v h) x * wScaled ℓ (g0 v h) y / ‖x - y‖))
        ≤ ∫⁻ y : ℝ³, ENNReal.ofReal (1 + S * (R / ℓ) ^ 2) * ENNReal.ofReal
            (wScaled ℓ (g0 v h) x * g0 v h y / ‖x - y‖) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hWy] with y hy
          have h1 : wScaled ℓ (g0 v h) x * wScaled ℓ (g0 v h) y
              ≤ wScaled ℓ (g0 v h) x * ((1 + S * (R / ℓ) ^ 2) * g0 v h y) :=
            mul_le_mul_of_nonneg_left hy hx
          have h2 : wScaled ℓ (g0 v h) x * wScaled ℓ (g0 v h) y / ‖x - y‖
              ≤ (1 + S * (R / ℓ) ^ 2)
                * (wScaled ℓ (g0 v h) x * g0 v h y / ‖x - y‖) := by
            have h3 := div_le_div_of_nonneg_right h1 (norm_nonneg (x - y))
            calc wScaled ℓ (g0 v h) x * wScaled ℓ (g0 v h) y / ‖x - y‖
                ≤ wScaled ℓ (g0 v h) x * ((1 + S * (R / ℓ) ^ 2) * g0 v h y) / ‖x - y‖ :=
                  h3
              _ = (1 + S * (R / ℓ) ^ 2)
                    * (wScaled ℓ (g0 v h) x * g0 v h y / ‖x - y‖) := by ring
          calc ENNReal.ofReal (wScaled ℓ (g0 v h) x * wScaled ℓ (g0 v h) y / ‖x - y‖)
              ≤ ENNReal.ofReal ((1 + S * (R / ℓ) ^ 2)
                  * (wScaled ℓ (g0 v h) x * g0 v h y / ‖x - y‖)) :=
                ENNReal.ofReal_le_ofReal h2
            _ = ENNReal.ofReal (1 + S * (R / ℓ) ^ 2) * ENNReal.ofReal
                  (wScaled ℓ (g0 v h) x * g0 v h y / ‖x - y‖) :=
                ENNReal.ofReal_mul hCnn
      _ = ENNReal.ofReal (1 + S * (R / ℓ) ^ 2) * (∫⁻ y : ℝ³, ENNReal.ofReal
            (wScaled ℓ (g0 v h) x * g0 v h y / ‖x - y‖)) :=
          lintegral_const_mul' _ _ (by simp)
  calc (∫⁻ x : ℝ³, ∫⁻ y : ℝ³,
        ENNReal.ofReal (wScaled ℓ (g0 v h) x * wScaled ℓ (g0 v h) y / ‖x - y‖))
      ≤ ∫⁻ x : ℝ³, ENNReal.ofReal (1 + S * (R / ℓ) ^ 2) * (∫⁻ y : ℝ³, ENNReal.ofReal
          (wScaled ℓ (g0 v h) x * g0 v h y / ‖x - y‖)) :=
        lintegral_mono_ae ((wScaled_g0_nonneg_ae (v := v) (R := R) hR hv hvrad hv_supp h).mono
          (fun x hx => hinner x hx))
    _ = ENNReal.ofReal (1 + S * (R / ℓ) ^ 2) * ∫⁻ x : ℝ³, ∫⁻ y : ℝ³,
        ENNReal.ofReal (wScaled ℓ (g0 v h) x * g0 v h y / ‖x - y‖) :=
        lintegral_const_mul' _ _ (by simp)

/-! ## 3. The main theorem -/

theorem massDeficit_taylor {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hvrad : BoseGases.IsRadial v) {R ℓ S : ℝ} (hR : 0 < R) (hℓ : 0 < ℓ)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) (hS : 0 ≤ S)
    (hconv : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ R →
        (1 - Submission.BoseGases.convScale ℓ x) / Submission.BoseGases.convScale ℓ x
          ≤ S * (‖x‖ / ℓ) ^ 2)
    (hW : MeasureTheory.Integrable (Work.BoseFixR.W1fun v h ℓ)) :
    ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : EuclideanSpace ℝ (Fin 3),
        (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) q) ^ 2 / (2 * ‖q‖ ^ 2)
      ≤ (1 + S * (R / ℓ) ^ 2) * ∫ x : EuclideanSpace ℝ (Fin 3),
          Work.BoseFixR.W1omegaFun v h ℓ x := by
  change ((2 * Real.pi) ^ 3)⁻¹ * (∫ q : ℝ³, (chat (wScaled ℓ (g0 v h)) q) ^ 2 / (2 * ‖q‖ ^ 2))
      ≤ (1 + S * (R / ℓ) ^ 2) * (∫ x : ℝ³, W1omegaFun v h ℓ x)
  set C : ℝ := 1 + S * (R / ℓ) ^ 2 with hCdef
  have hCnn : 0 ≤ C := by
    rw [hCdef]
    have := mul_nonneg hS (sq_nonneg (R / ℓ))
    linarith
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
  have hPA := lintegral_W1W1_le_oneAddS_W1g0 (v := v) h hv hvrad hR hℓ hv_supp hRℓ hS hconv
  have hPB := lintegral_W1_g0_eq (v := v) h (R := R) (ℓ := ℓ) hR hv hvrad hv_supp hRℓ hℓ
  rw [← hCdef] at hPA
  -- the arithmetic of the two explicit constants
  have hAB : ENNReal.ofReal (1 / (4 * Real.pi)) * ENNReal.ofReal (8 * Real.pi) = (2 : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 / (4 * Real.pi))]
    have hval : (1 / (4 * Real.pi)) * (8 * Real.pi) = 2 := by
      have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
      field_simp
      norm_num
    rw [hval]
    norm_num
  have hhalf2 : (1 / 2 : ℝ≥0∞) * 2 = 1 := by
    have h := ENNReal.inv_mul_cancel (a := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
    simpa using h
  have key : ENNReal.ofReal (((2 * Real.pi) ^ 3)⁻¹)
        * (∫⁻ q : ℝ³, ENNReal.ofReal ((chat (wScaled ℓ (g0 v h)) q) ^ 2 / (2 * ‖q‖ ^ 2)))
      ≤ ENNReal.ofReal (C * ∫ x : ℝ³,
          wScaled ℓ (g0 v h) x * Classical.choose h x) := by
    have hstep1 := lintegral_chat_le_kinFT (wScaled ℓ (g0 v h))
    calc ENNReal.ofReal (((2 * Real.pi) ^ 3)⁻¹)
          * (∫⁻ q : ℝ³, ENNReal.ofReal ((chat (wScaled ℓ (g0 v h)) q) ^ 2 / (2 * ‖q‖ ^ 2)))
        ≤ ENNReal.ofReal (((2 * Real.pi) ^ 3)⁻¹)
            * ((1 / 2 : ℝ≥0∞) * (∫⁻ q : ℝ³, ENNReal.ofReal
                (‖kinFT (fun y : ℝ³ => ((wScaled ℓ (g0 v h) y : ℝ) : ℂ)) q‖ ^ 2
                  / ‖q‖ ^ 2))) := mul_le_mul_left_ennrealS hstep1
        _ = (1 / 2 : ℝ≥0∞) * (ENNReal.ofReal (((2 * Real.pi) ^ 3)⁻¹)
            * (∫⁻ q : ℝ³, ENNReal.ofReal
                (‖kinFT (fun y : ℝ³ => ((wScaled ℓ (g0 v h) y : ℝ) : ℂ)) q‖ ^ 2
                  / ‖q‖ ^ 2))) := by ring
        _ ≤ (1 / 2 : ℝ≥0∞) * (ENNReal.ofReal (1 / (4 * Real.pi))
            * (∫⁻ x : ℝ³, ∫⁻ y : ℝ³, ENNReal.ofReal
                (wScaled ℓ (g0 v h) x * wScaled ℓ (g0 v h) y / ‖x - y‖))) :=
          mul_le_mul_left_ennrealS hfour
        _ ≤ (1 / 2 : ℝ≥0∞) * (ENNReal.ofReal (1 / (4 * Real.pi))
            * (ENNReal.ofReal C * (∫⁻ x : ℝ³, ∫⁻ y : ℝ³, ENNReal.ofReal
                (wScaled ℓ (g0 v h) x * g0 v h y / ‖x - y‖)))) :=
          mul_le_mul_left_ennrealS (mul_le_mul_left_ennrealS hPA)
        _ = (1 / 2 : ℝ≥0∞) * (ENNReal.ofReal (1 / (4 * Real.pi))
            * (ENNReal.ofReal C * (ENNReal.ofReal (8 * Real.pi)
                * ENNReal.ofReal (∫ x : ℝ³,
                    wScaled ℓ (g0 v h) x * Classical.choose h x)))) := by rw [hPB]
        _ = ENNReal.ofReal C * ENNReal.ofReal (∫ x : ℝ³,
                wScaled ℓ (g0 v h) x * Classical.choose h x) := by
              rw [show (1 / 2 : ℝ≥0∞) * (ENNReal.ofReal (1 / (4 * Real.pi))
                    * (ENNReal.ofReal C * (ENNReal.ofReal (8 * Real.pi)
                      * ENNReal.ofReal (∫ x : ℝ³,
                          wScaled ℓ (g0 v h) x * Classical.choose h x))))
                  = ((1 / 2 : ℝ≥0∞) * (ENNReal.ofReal (1 / (4 * Real.pi))
                      * ENNReal.ofReal (8 * Real.pi)))
                    * (ENNReal.ofReal C * ENNReal.ofReal (∫ x : ℝ³,
                        wScaled ℓ (g0 v h) x * Classical.choose h x)) from by ring,
                hAB, hhalf2, one_mul]
        _ = ENNReal.ofReal (C * ∫ x : ℝ³,
                wScaled ℓ (g0 v h) x * Classical.choose h x) :=
              (ENNReal.ofReal_mul hCnn).symm
  -- the Bochner integral as a `toReal` of the corresponding lintegral
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
    _ ≤ (ENNReal.ofReal (C * ∫ x : ℝ³,
          wScaled ℓ (g0 v h) x * Classical.choose h x)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top key
    _ = C * ∫ x : ℝ³, wScaled ℓ (g0 v h) x * Classical.choose h x :=
        ENNReal.toReal_ofReal (mul_nonneg hCnn hMnn)
    _ = C * ∫ x : ℝ³, W1omegaFun v h ℓ x := by
        rw [mass_eq v h ℓ]
        rfl
    _ = (1 + S * (R / ℓ) ^ 2) * ∫ x : ℝ³, W1omegaFun v h ℓ x := by rw [hCdef]

end Work.BoseFixR
