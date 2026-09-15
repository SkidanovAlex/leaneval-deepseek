import Mathlib
import Submission.Vinogradov.Nikolskii
import Submission.Commons.Measure.Integral.setIntegral_ball_swap
import Submission.Commons.Analysis.Integral.jensen_rpow_prob
import Submission.Commons.Analysis.Integral.integrable_and_integral_one_add_norm_neg_mul_le
import Submission.Commons.Analysis.Distribution.schwartzMap_decay_one_add_norm

noncomputable section
open MeasureTheory Complex
open scoped Real BigOperators FourierTransform RealInnerProductSpace Interval

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Vinogradov

open Classical

/-!
# The global `L^q(w_B)`–`L^p(w_B)` comparison for the extension operator (BDG §7)

This module proves the Corollary after Lemma `nl9` of Bourgain–Demeter–Guth
(the "ε-removal"-free Nikolskii comparison of weighted norms):

    ‖E_{[0,1]} g‖_{L^q(w_B)} ≲ ‖E_{[0,1]} g‖_{L^p(w_B)}      (R ≥ 1, q ≥ p > 1),

with a constant depending only on `k, p, q`.  The ingredients are

* the two-sided local comparability of the ball weight `w_B` at scale `R`
  (`ballWeight_le_two_pow_mul`, `integral_ball_ge`, `integral_ball_le`),
* the inside-ball bound `extOp_ball_Lq_le` (proved in `Nikolskii.lean`),
* Fubini (to pass from the ball average of the weight to the ball `B(c',R)`),
* weighted Jensen (`Commons.Analysis.Integral.jensen_rpow_prob`), and
* the weight-transfer estimate `ballWeight_transfer`
  (`∫_{c'} w_B(c') ‖φ_{B(c',R)}(y)‖^p dc' ≲ Rᵏ w_B(y)`, from the Schwartz decay
  of `φ` and the convolution-of-decaying-kernels lemma).

Everything is proved (no sorries).
-/

/-- The ball weight in real-power form: for `R > 0`,
`w_B(x) = (1 + ‖x - c‖/R)^{-100k}`. -/
lemma ballWeight_eq_rpow (k : ℕ) (c : E k) {R : ℝ} (hR : 0 < R) (x : E k) :
    ballWeight k c R x = (1 + ‖x - c‖ / R) ^ (-(100 * k : ℝ)) := by
  unfold ballWeight
  have hb : 0 < 1 + ‖x - c‖ / R := by
    have := norm_nonneg (x - c); positivity
  have h : (1 + ‖x - c‖ / R) ^ (-(100 * k : ℝ))
      = ((1 + ‖x - c‖ / R) ^ (100 * k))⁻¹ := by
    rw [Real.rpow_neg (le_of_lt hb)]
    congr 1
    rw [show (100 * k : ℝ) = ((100 * k : ℕ) : ℝ) from by push_cast; ring,
      Real.rpow_natCast]
  exact h.symm

lemma four_pow_eq (k : ℕ) : (4:ℝ)^(100*k) = (2:ℝ)^(200*k) := by
  have h1 : (4:ℝ)^(100*k) = ((2:ℝ)^2)^(100*k) := by norm_num
  rw [h1, ← pow_mul]
  ring

/-- Two-sided local comparability (upper direction): if `‖x - c'‖ ≤ R` then
`w_B(x) ≤ 2^{100k} w_B(c')`. -/
lemma ballWeight_le_two_pow_mul (k : ℕ) (c : E k) {R : ℝ} (hR : 0 < R) {c' x : E k}
    (h : ‖x - c'‖ ≤ R) :
    ballWeight k c R x ≤ (2:ℝ)^(100*k) * ballWeight k c R c' := by
  have hx : 0 < 1 + ‖x - c‖ / R := by have := norm_nonneg (x - c); positivity
  have hc : 0 < 1 + ‖c' - c‖ / R := by have := norm_nonneg (c' - c); positivity
  have hle : 1 + ‖c' - c‖ / R ≤ 2 * (1 + ‖x - c‖ / R) := by
    have h1 : ‖c' - c‖ ≤ ‖c' - x‖ + ‖x - c‖ := by
      simpa [sub_add_sub_cancel] using norm_add_le (c' - x) (x - c)
    have h2 : ‖c' - x‖ ≤ R := by rw [norm_sub_rev]; exact h
    have h3 : ‖c' - c‖ / R ≤ (R + ‖x - c‖) / R :=
      div_le_div_of_nonneg_right (by linarith) (le_of_lt hR)
    have h4 : (R + ‖x - c‖) / R = 1 + ‖x - c‖ / R := by field_simp
    have hb : 1 ≤ 1 + ‖x - c‖ / R := by
      have := norm_nonneg (x - c)
      have : 0 ≤ ‖x - c‖ / R := div_nonneg this (le_of_lt hR)
      linarith
    linarith [h3, h4.ge, h4.le]
  have hpow : (1 + ‖c' - c‖ / R)^(100*k) ≤ (2 * (1 + ‖x - c‖ / R))^(100*k) :=
    pow_le_pow_left₀ (le_of_lt hc) hle _
  rw [mul_pow] at hpow
  have step : ((2:ℝ)^(100*k) * (1 + ‖x - c‖ / R)^(100*k))⁻¹
      ≤ ((1 + ‖c' - c‖ / R)^(100*k))⁻¹ :=
    (inv_le_inv₀ (by positivity) (pow_pos hc _)).mpr hpow
  rw [mul_inv] at step
  unfold ballWeight
  calc ((1 + ‖x - c‖ / R) ^ (100 * k))⁻¹
      = (2:ℝ)^(100*k) * ((2:ℝ)^(100*k))⁻¹ * ((1 + ‖x - c‖ / R) ^ (100 * k))⁻¹ := by
        field_simp
    _ = (2:ℝ)^(100*k) * (((2:ℝ)^(100*k))⁻¹ * ((1 + ‖x - c‖ / R) ^ (100 * k))⁻¹) := by ring
    _ ≤ (2:ℝ)^(100*k) * ((1 + ‖c' - c‖ / R) ^ (100 * k))⁻¹ :=
        mul_le_mul_of_nonneg_left step (by positivity)

/-- Two-sided local comparability (lower direction): if `‖x - c'‖ ≤ R` then
`w_B(c') ≤ 2^{200k} w_B(x)`. -/
lemma ballWeight_le_const_mul (k : ℕ) (c : E k) {R : ℝ} (hR : 0 < R) {x y : E k}
    (h : ‖x - y‖ ≤ R) :
    ballWeight k c R y ≤ (2:ℝ)^(200*k) * ballWeight k c R x := by
  have hx : 0 < 1 + ‖x - c‖ / R := by have := norm_nonneg (x - c); positivity
  have hy : 0 < 1 + ‖y - c‖ / R := by have := norm_nonneg (y - c); positivity
  have h4 : 1 + ‖x - c‖ / R ≤ 4 * (1 + ‖y - c‖ / R) := by
    have h1 : ‖x - c‖ ≤ ‖x - y‖ + ‖y - c‖ := by
      simpa [sub_add_sub_cancel] using norm_add_le (x - y) (y - c)
    have h3 : ‖x - c‖ / R ≤ (R + ‖y - c‖) / R :=
      div_le_div_of_nonneg_right (by linarith) (le_of_lt hR)
    have h4 : (R + ‖y - c‖) / R = 1 + ‖y - c‖ / R := by field_simp
    have hb : 1 ≤ 1 + ‖y - c‖ / R := by
      have := norm_nonneg (y - c)
      have : 0 ≤ ‖y - c‖ / R := div_nonneg this (le_of_lt hR)
      linarith
    linarith [h3, h4.ge, h4.le]
  have hpow : (1 + ‖x - c‖ / R)^(100*k) ≤ (4 * (1 + ‖y - c‖ / R))^(100*k) :=
    pow_le_pow_left₀ (le_of_lt hx) h4 _
  rw [mul_pow] at hpow
  have step : ((4:ℝ)^(100*k) * (1 + ‖y - c‖ / R)^(100*k))⁻¹
      ≤ ((1 + ‖x - c‖ / R)^(100*k))⁻¹ :=
    (inv_le_inv₀ (by positivity) (pow_pos hx _)).mpr hpow
  rw [mul_inv] at step
  unfold ballWeight
  calc ((1 + ‖y - c‖ / R) ^ (100 * k))⁻¹
      = (2:ℝ)^(200*k) * (((4:ℝ)^(100*k))⁻¹ * ((1 + ‖y - c‖ / R) ^ (100 * k))⁻¹) := by
        rw [four_pow_eq]; field_simp
    _ ≤ (2:ℝ)^(200*k) * ((1 + ‖x - c‖ / R) ^ (100 * k))⁻¹ :=
        mul_le_mul_of_nonneg_left step (by positivity)

/-- Lower bound on the ball integral of the weight: `∫_{B(x,R)} w_B ≳ Rᵏ w_B(x)`. -/
lemma integral_ball_ge (k : ℕ) (hk : 1 ≤ k) (c : E k) {R : ℝ} (hR : 0 < R) (x : E k) :
    ((2:ℝ)^(100*k))⁻¹ * ballWeight k c R x * ballVol k x R
      ≤ ∫ y in Metric.ball x R, ballWeight k c R y := by
  have h2k : 0 < (2:ℝ)^(100*k) := by positivity
  have hpt : ∀ y ∈ Metric.ball x R, ((2:ℝ)^(100*k))⁻¹ * ballWeight k c R x ≤ ballWeight k c R y := by
    intro y hy
    have hxy : ‖x - y‖ ≤ R := by
      have h := hy
      rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev] at h
      exact le_of_lt h
    have h := ballWeight_le_two_pow_mul k c hR (c' := y) (x := x) hxy
    calc ((2:ℝ)^(100*k))⁻¹ * ballWeight k c R x
        ≤ ((2:ℝ)^(100*k))⁻¹ * ((2:ℝ)^(100*k) * ballWeight k c R y) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = ballWeight k c R y := by field_simp
  have hconst : ∫ _y in Metric.ball x R, ((2:ℝ)^(100*k))⁻¹ * ballWeight k c R x
      = ((2:ℝ)^(100*k))⁻¹ * ballWeight k c R x * ballVol k x R := by
    rw [setIntegral_const, smul_eq_mul, MeasureTheory.measureReal_def, ballVol]
    ring
  rw [← hconst]
  refine setIntegral_mono_on ?_ ?_ measurableSet_ball hpt
  · exact integrableOn_const (measure_ball_lt_top.ne)
  · exact (ballWeight_integrable k hk c hR).integrableOn

/-- Upper bound on the ball integral of the weight: `∫_{B(x,R)} w_B ≲ Rᵏ w_B(x)`. -/
lemma integral_ball_le (k : ℕ) (hk : 1 ≤ k) (c : E k) {R : ℝ} (hR : 0 < R) (x : E k) :
    ∫ y in Metric.ball x R, ballWeight k c R y
      ≤ (2:ℝ)^(200*k) * ballWeight k c R x * ballVol k x R := by
  have hpt : ∀ y ∈ Metric.ball x R, ballWeight k c R y
      ≤ (2:ℝ)^(200*k) * ballWeight k c R x := fun y hy =>
    ballWeight_le_const_mul k c hR (by
      have h := hy
      rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev] at h
      exact le_of_lt h)
  have hconst : ∫ _y in Metric.ball x R, (2:ℝ)^(200*k) * ballWeight k c R x
      = (2:ℝ)^(200*k) * ballWeight k c R x * ballVol k x R := by
    rw [setIntegral_const, smul_eq_mul, MeasureTheory.measureReal_def, ballVol]
    ring
  rw [← hconst]
  refine setIntegral_mono_on ?_ ?_ measurableSet_ball hpt
  · exact (ballWeight_integrable k hk c hR).integrableOn
  · exact integrableOn_const (measure_ball_lt_top.ne)

/-- Normalisation identity in the transfer estimate:
`‖y - R•v - c‖ / R = ‖R⁻¹ • (y - c) - v‖` (for `R > 0`). -/
lemma norm_scaled_sub (k : ℕ) (c y v : E k) {R : ℝ} (hR : 0 < R) :
    ‖y - R • v - c‖ / R = ‖(R⁻¹ : ℝ) • (y - c) - v‖ := by
  have h1 : y - R • v - c = (y - c) - R • v := by abel
  have h2 : (R⁻¹ : ℝ) • ((y - c) - R • v) = (R⁻¹ : ℝ) • (y - c) - v := by
    rw [smul_sub, inv_smul_smul₀ hR.ne']
  rw [h1, ← h2, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hR.le),
    inv_mul_eq_div]

/-- Schwartz decay of the localizing kernel in the form needed for the transfer:
`‖ψ v‖^P ≤ C (1 + ‖v‖)^{-100k}` for `P ≥ 1`. -/
lemma schwartz_decay_rpow {k : ℕ} {P : ℝ} (hP : 1 ≤ P) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : E k,
      ‖(𝓕⁻ (freqBumpSch k) : SchwartzMap (E k) ℂ) v‖ ^ P
        ≤ C * (1 + ‖v‖) ^ (-(100*k : ℝ)) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ :=
    Commons.Analysis.Distribution.schwartzMap_decay_one_add_norm
      (𝓕⁻ (freqBumpSch k) : SchwartzMap (E k) ℂ) (100*k)
  refine ⟨C₀ ^ P, by positivity, fun v => ?_⟩
  have h1 : ‖(𝓕⁻ (freqBumpSch k) : SchwartzMap (E k) ℂ) v‖
      ≤ C₀ * (1 + ‖v‖) ^ (-((100*k : ℕ) : ℝ)) := hC₀ v
  have hb : 1 ≤ 1 + ‖v‖ := by have := norm_nonneg v; linarith
  have hb0 : (0:ℝ) < 1 + ‖v‖ := by linarith
  have hcast : ((100*k : ℕ) : ℝ) = 100 * (k : ℝ) := by push_cast; ring
  have hN : (0:ℝ) ≤ 100 * (k : ℝ) := by positivity
  calc ‖(𝓕⁻ (freqBumpSch k) : SchwartzMap (E k) ℂ) v‖ ^ P
      ≤ (C₀ * (1 + ‖v‖) ^ (-((100*k : ℕ) : ℝ))) ^ P :=
        Real.rpow_le_rpow (norm_nonneg _) h1 (by linarith)
    _ = C₀ ^ P * ((1 + ‖v‖) ^ (-((100*k : ℕ) : ℝ))) ^ P :=
        Real.mul_rpow hC₀pos.le (Real.rpow_nonneg (by linarith) _)
    _ = C₀ ^ P * (1 + ‖v‖) ^ (-((100*k : ℕ) : ℝ) * P) := by
        rw [Real.rpow_mul (by linarith)]
    _ ≤ C₀ ^ P * (1 + ‖v‖) ^ (-(100*k : ℝ)) := by
        have hexp : -((100*k : ℕ) : ℝ) * P ≤ -(100*k : ℝ) := by
          rw [hcast]
          have h1 : (0:ℝ) ≤ 100 * (k:ℝ) := by positivity
          have h2 : (100 * (k:ℝ)) * 1 ≤ (100*(k:ℝ)) * P := mul_le_mul_of_nonneg_left hP h1
          linarith
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hb hexp) (by positivity)

/-- Reflection/translation substitution: `∫ F(c') dc' = ∫ F(y - u) du`. -/
lemma integral_sub_left (k : ℕ) (y : E k) (F : E k → ℝ) (hF : AEStronglyMeasurable F volume) :
    ∫ c' : E k, F c' = ∫ u : E k, F (y - u) := by
  have hmp : MeasurePreserving (fun u : E k => y + (-u)) volume volume :=
    (measurePreserving_add_left volume y).comp (Measure.measurePreserving_neg volume)
  have hsm : AEStronglyMeasurable F (Measure.map (fun u : E k => y + (-u)) volume) := by
    rw [hmp.map_eq]; exact hF
  have hfun : (fun u : E k => F (y - u)) = (fun u : E k => F (y + (-u))) := by
    funext u; rw [sub_eq_add_neg]
  rw [hfun, ← MeasureTheory.integral_map hmp.aemeasurable hsm, hmp.map_eq]

/-- Scaling substitution: `∫ G(R⁻¹ • u) du = Rᵏ ∫ G v dv` for `R > 0`. -/
lemma integral_smul_inv (k : ℕ) {R : ℝ} (hR : 0 < R) (G : E k → ℝ) :
    ∫ u : E k, G (R⁻¹ • u) = R^k * ∫ v : E k, G v := by
  rw [MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg volume G hR.le,
    finrank_euclideanSpace, Fintype.card_fin]
  simp [smul_eq_mul]

/-- **Transfer estimate for the localizing weight** (the `η_B`-inequality in BDG's
Lemma nl9): there is `C > 0` (depending on `k` and `p`) with
`∫_{c'} w_B(c') ‖φ_{B(c',R)}(y)‖^p dc' ≤ C Rᵏ w_B(y)` for all `R > 0`, `c`, `y`. -/
lemma exists_ballWeight_transfer (k : ℕ) (hk : 1 ≤ k) {P : ℝ} (hP : 1 ≤ P) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : E k) {R : ℝ}, 0 < R → ∀ y : E k,
      ∫ c' : E k, ballWeight k c R c' * ‖phiB k c' R y‖ ^ P
        ≤ C * R^k * ballWeight k c R y := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := schwartz_decay_rpow (k := k) hP
  have hAc : (k:ℝ) < (100*k : ℝ) := by
    have hkR : (0:ℝ) < k := by exact_mod_cast hk
    nlinarith
  obtain ⟨C₁, hC₁pos, hC₁⟩ :=
    Commons.Analysis.Integral.integrable_and_integral_one_add_norm_neg_mul_le
      (k := k) (A := (100*k : ℝ)) (B := (100*k : ℝ)) hAc hAc
  refine ⟨C₀ * C₁, by positivity, ?_⟩
  intro c R hR y
  set H : E k → ℝ := fun c' => ballWeight k c R c' * ‖phiB k c' R y‖ ^ P with hH
  set G : E k → ℝ := fun v => ballWeight k c R (y - R • v)
      * ‖(𝓕⁻ (freqBumpSch k) : SchwartzMap (E k) ℂ) v‖ ^ P with hG
  set z : E k := (R⁻¹:ℝ) • (y - c) with hz
  -- (i) reflection/translation
  have hHmeas : AEStronglyMeasurable H volume := by
    have hcont1 : Continuous (fun c' : E k => phiB k c' R y) := by
      have h1 : Continuous (fun c' : E k =>
          (𝓕⁻ (freqBumpSch k) : SchwartzMap (E k) ℂ) ((R⁻¹:ℝ) • (y - c'))) :=
        ((𝓕⁻ (freqBumpSch k) : SchwartzMap (E k) ℂ)).continuous.comp (by fun_prop)
      exact h1.congr (fun c' => (phiB_eq_schwartz k c' R y).symm)
    have : Continuous H := by
      simp only [hH]
      exact (ballWeight_continuous k c hR).mul
        (hcont1.norm.rpow_const (fun x => Or.inr (by positivity)))
    exact this.aestronglyMeasurable
  have h1 : ∫ c' : E k, H c' = ∫ u : E k, H (y - u) := integral_sub_left k y H hHmeas
  -- (ii) collapse `phiB` and rescale
  have h2 : (fun u : E k => H (y - u)) = fun u : E k => G ((R⁻¹:ℝ) • u) := by
    funext u
    simp only [hH, hG]
    rw [phiB_eq_schwartz]
    have e : y - (y - u) = u := by abel
    rw [e, smul_inv_smul₀ hR.ne']
  have h3 : ∫ u : E k, G ((R⁻¹:ℝ) • u) = R^k * ∫ v : E k, G v := integral_smul_inv k hR G
  -- (iii) rewrite the weight in `G`
  have h4 : ∫ v : E k, G v
      = ∫ v : E k, (1 + ‖z - v‖) ^ (-(100*k:ℝ))
          * ‖(𝓕⁻ (freqBumpSch k) : SchwartzMap (E k) ℂ) v‖ ^ P := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [hG, hz]
    rw [ballWeight_eq_rpow k c hR (y - R • v), norm_scaled_sub k c y v hR]
  -- (iv) Schwartz decay and the convolution bound
  have hInt : Integrable (fun v : E k => (1 + ‖z - v‖) ^ (-(100*k:ℝ))
      * (C₀ * (1 + ‖v‖) ^ (-(100*k:ℝ)))) volume := by
    have h := (hC₁ z).1
    have h' : Integrable (fun u : E k => C₀ * ((1 + ‖u‖) ^ (-(100*k:ℝ))
        * (1 + ‖z - u‖) ^ (-(100*k:ℝ)))) volume := h.const_mul C₀
    refine h'.congr (Filter.Eventually.of_forall fun v => ?_)
    ring
  have h5 : ∫ v : E k, (1 + ‖z - v‖) ^ (-(100*k:ℝ))
        * ‖(𝓕⁻ (freqBumpSch k) : SchwartzMap (E k) ℂ) v‖ ^ P
      ≤ ∫ v : E k, (1 + ‖z - v‖) ^ (-(100*k:ℝ))
          * (C₀ * (1 + ‖v‖) ^ (-(100*k:ℝ))) := by
    refine integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun v => mul_nonneg
        (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (norm_nonneg _) _)) hInt
      (Filter.Eventually.of_forall fun v => ?_)
    exact mul_le_mul_of_nonneg_left (hC₀ v) (Real.rpow_nonneg (by positivity) _)
  have hfac : ∫ v : E k, (1 + ‖z - v‖) ^ (-(100*k:ℝ)) * (C₀ * (1 + ‖v‖) ^ (-(100*k:ℝ)))
      = C₀ * ∫ v : E k, (1 + ‖v‖) ^ (-(100*k:ℝ)) * (1 + ‖z - v‖) ^ (-(100*k:ℝ)) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    ring
  have hconv : ∫ v : E k, (1 + ‖v‖) ^ (-(100*k:ℝ)) * (1 + ‖z - v‖) ^ (-(100*k:ℝ))
      ≤ C₁ * (1 + ‖z‖) ^ (-(100*k:ℝ)) := by
    have h := (hC₁ z).2
    rw [min_self] at h
    exact h
  have hzb : (1 + ‖z‖) ^ (-(100*k:ℝ)) = ballWeight k c R y := by
    rw [ballWeight_eq_rpow k c hR y]
    congr 2
    rw [hz, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hR.le), inv_mul_eq_div]
  have hmain : ∫ v : E k, (1 + ‖z - v‖) ^ (-(100*k:ℝ))
        * ‖(𝓕⁻ (freqBumpSch k) : SchwartzMap (E k) ℂ) v‖ ^ P
      ≤ C₀ * C₁ * ballWeight k c R y := by
    calc ∫ v : E k, (1 + ‖z - v‖) ^ (-(100*k:ℝ))
          * ‖(𝓕⁻ (freqBumpSch k) : SchwartzMap (E k) ℂ) v‖ ^ P
        ≤ C₀ * ∫ v : E k, (1 + ‖v‖) ^ (-(100*k:ℝ)) * (1 + ‖z - v‖) ^ (-(100*k:ℝ)) :=
          h5.trans (le_of_eq hfac)
      _ ≤ C₀ * (C₁ * (1 + ‖z‖) ^ (-(100*k:ℝ))) :=
          mul_le_mul_of_nonneg_left hconv hC₀pos.le
      _ = C₀ * C₁ * ballWeight k c R y := by rw [hzb]; ring
  calc ∫ c' : E k, ballWeight k c R c' * ‖phiB k c' R y‖ ^ P
      = ∫ c' : E k, H c' := by rw [hH]
    _ = ∫ u : E k, G ((R⁻¹:ℝ) • u) := by rw [h1, h2]
    _ = R^k * ∫ v : E k, G v := h3
    _ = R^k * ∫ v : E k, (1 + ‖z - v‖) ^ (-(100*k:ℝ))
          * ‖(𝓕⁻ (freqBumpSch k) : SchwartzMap (E k) ℂ) v‖ ^ P := by rw [h4]
    _ ≤ R^k * (C₀ * C₁ * ballWeight k c R y) :=
          mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = C₀ * C₁ * R^k * ballWeight k c R y := by ring

/-- **Symmetry of the ball average** (Fubini for the symmetric ball relation) —
the shared-commons version `Commons.Measure.Integral.setIntegral_ball_swap`. -/
lemma setIntegral_ball_swap (k : ℕ) (F W : E k → ℝ) (hFm : Measurable F) (hWm : Measurable W)
    (hF0 : 0 ≤ F) (hW0 : 0 ≤ W) {M : ℝ} (hM : ∀ x, F x ≤ M)
    (hWint : Integrable W volume) {R : ℝ} {KW : ℝ} (hKW0 : 0 ≤ KW)
    (hKW : ∀ x : E k, (∫ c' in Metric.ball x R, W c') ≤ KW * W x) :
    (∫ x : E k, F x * (∫ c' in Metric.ball x R, W c'))
      = ∫ c' : E k, W c' * (∫ x in Metric.ball c' R, F x) :=
  Commons.Measure.Integral.setIntegral_ball_swap k F W hFm hWm hF0 hW0 hM hWint hKW0 hKW

/-- Pointwise lower bound for the ball weight by its ball average (the local-average step
of BDG's Lemma nl9): `w_B(x) ≲ R^{-k} ∫_{B(x,R)} w_B`. -/
lemma ballWeight_le_ball_average (k : ℕ) (hk : 1 ≤ k) (c : E k) {R : ℝ} (hR : 0 < R) (x : E k) :
    ballWeight k c R x ≤ ((2:ℝ)^(100*k) / ballVol k 0 1) * (R^k)⁻¹
      * ∫ y in Metric.ball x R, ballWeight k c R y := by
  have h := integral_ball_ge k hk c hR x
  have hV : ballVol k x R = R^k * ballVol k 0 1 := ballVol_smul k hk x (le_of_lt hR)
  have hV0 : 0 < ballVol k 0 1 := ballVol_pos k hk 0 (by norm_num)
  rw [hV] at h
  calc ballWeight k c R x
      = ((2:ℝ)^(100*k) * ((R^k * ballVol k 0 1))⁻¹)
          * (((2:ℝ)^(100*k))⁻¹ * ballWeight k c R x * (R^k * ballVol k 0 1)) := by
        field_simp
    _ ≤ ((2:ℝ)^(100*k) * ((R^k * ballVol k 0 1))⁻¹)
          * ∫ y in Metric.ball x R, ballWeight k c R y :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = ((2:ℝ)^(100*k) / ballVol k 0 1) * (R^k)⁻¹
          * ∫ y in Metric.ball x R, ballWeight k c R y := by
        field_simp

/-- Pointwise upper bound for the ball average of the weight (used for the joint
integrability in the ball-average symmetry): `∫_{B(x,R)} w_B ≲ Rᵏ w_B(x)`. -/
lemma ballAverage_le (k : ℕ) (hk : 1 ≤ k) (c : E k) {R : ℝ} (hR : 0 < R) (x : E k) :
    (∫ y in Metric.ball x R, ballWeight k c R y)
      ≤ ((2:ℝ)^(200*k) * (R^k * ballVol k 0 1)) * ballWeight k c R x := by
  have h := integral_ball_le k hk c hR x
  have hV : ballVol k x R = R^k * ballVol k 0 1 := ballVol_smul k hk x (le_of_lt hR)
  rw [hV] at h
  calc (∫ y in Metric.ball x R, ballWeight k c R y)
      ≤ (2:ℝ)^(200*k) * ballWeight k c R x * (R^k * ballVol k 0 1) := h
    _ = ((2:ℝ)^(200*k) * (R^k * ballVol k 0 1)) * ballWeight k c R x := by ring

/-- Measurability of the ball average `x ↦ ∫_{B(x,R)} W(x)`. -/
lemma measurable_ballAverage (k : ℕ) (W : E k → ℝ) (hW : Measurable W) (R : ℝ) :
    Measurable (fun x : E k => ∫ y in Metric.ball x R, W y) := by
  have hD : MeasurableSet {p : E k × E k | dist p.1 p.2 < R} :=
    measurableSet_lt measurable_dist measurable_const
  have hg : Measurable (fun p : E k × E k =>
      {p : E k × E k | dist p.1 p.2 < R}.indicator (fun p => W p.2) p) :=
    (hW.comp measurable_snd).indicator hD
  have hmeas : Measurable (fun x : E k => ∫ y : E k,
      {p : E k × E k | dist p.1 p.2 < R}.indicator (fun p => W p.2) (x,y)) :=
    (hg.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure (E k)))).measurable
  have hfun : (fun x : E k => ∫ y in Metric.ball x R, W y)
      = fun x : E k => ∫ y : E k,
        {p : E k × E k | dist p.1 p.2 < R}.indicator (fun p => W p.2) (x,y) := by
    funext x
    rw [(MeasureTheory.integral_indicator measurableSet_ball).symm]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, Metric.mem_ball]
    by_cases h2 : dist y x < R
    · rw [if_pos h2, if_pos (by rwa [dist_comm] at h2)]
    · rw [if_neg h2, if_neg (by rwa [dist_comm] at h2)]
  rw [hfun]
  exact hmeas

/-- **The local-average step of BDG's Lemma nl9.** -/
lemma local_average_step (k : ℕ) (hk : 1 ≤ k) (g : ℝ → ℂ) (hg : IntegrableOn g (Set.Icc (0:ℝ) 1) volume)
    {Q : ℝ} (hQ : 0 ≤ Q) (c : E k) {R : ℝ} (hR : 1 ≤ R) :
    ∫ x : E k, ‖extOp k g 0 1 x‖ ^ Q * ballWeight k c R x
      ≤ ((2:ℝ)^(100*k) / ballVol k 0 1) * (R^k)⁻¹
        * ∫ c' : E k, ballWeight k c R c' * (∫ x in Metric.ball c' R, ‖extOp k g 0 1 x‖ ^ Q) := by
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
  have hV0 : 0 < ballVol k 0 1 := ballVol_pos k hk 0 (by norm_num)
  have hKc : 0 < ((2:ℝ)^(100*k) / ballVol k 0 1) * (R^k)⁻¹ := by positivity
  set F : E k → ℝ := fun x => ‖extOp k g 0 1 x‖ ^ Q with hF
  set W : E k → ℝ := ballWeight k c R with hW
  have hFnn : 0 ≤ F := by intro x; rw [hF]; exact Real.rpow_nonneg (norm_nonneg _) Q
  have hFm : Measurable F := by
    rw [hF]
    exact ((continuous_extOp k g hg).norm.rpow_const (fun x => Or.inr hQ)).measurable
  have hWm : Measurable W := by rw [hW]; exact (ballWeight_continuous k c hR0).measurable
  have hWnn : 0 ≤ W := by intro x; rw [hW]; exact le_of_lt (ballWeight_pos k c hR0 x)
  have hWint : Integrable W volume := by rw [hW]; exact ballWeight_integrable k hk c hR0
  -- bound for `F`
  set M : ℝ := ∫ t in (0:ℝ)..1, ‖g t‖ with hMdef
  have hFbound : ∀ x, F x ≤ M ^ Q := by
    intro x
    have h1 : ‖extOp k g 0 1 x‖ ≤ M := by
      rw [hMdef, extOp]
      calc ‖∫ t in (0:ℝ)..1, g t * momChar k x t‖
          ≤ ∫ t in (0:ℝ)..1, ‖g t * momChar k x t‖ :=
            intervalIntegral.norm_integral_le_integral_norm (by norm_num)
        _ = ∫ t in (0:ℝ)..1, ‖g t‖ := by
            refine intervalIntegral.integral_congr fun t _ => ?_
            rw [norm_mul, momChar_norm_one, mul_one]
    have h2 : (0:ℝ) ≤ ‖extOp k g 0 1 x‖ := norm_nonneg _
    calc F x = ‖extOp k g 0 1 x‖ ^ Q := by simp only [hF]
      _ ≤ M ^ Q := Real.rpow_le_rpow h2 h1 hQ
  have hM0 : 0 ≤ M := by
    rw [hMdef]; exact intervalIntegral.integral_nonneg (by norm_num) (fun t _ => norm_nonneg _)
  -- the two-sided ball-average bounds
  have hKW : ∀ x : E k, (∫ y in Metric.ball x R, W y) ≤
      ((2:ℝ)^(200*k) * (R^k * ballVol k 0 1)) * W x := by
    intro x
    rw [hW]
    exact ballAverage_le k hk c hR0 x
  have hKW0 : 0 ≤ (2:ℝ)^(200*k) * (R^k * ballVol k 0 1) := by
    have hV0 : 0 < ballVol k 0 1 := ballVol_pos k hk 0 (by norm_num)
    positivity
  -- the swap
  have hswap := setIntegral_ball_swap k F W hFm hWm hFnn hWnn hFbound hWint hKW0 hKW
  -- pointwise local average
  have hpt : ∀ x : E k, F x * W x ≤ F x * (((2:ℝ)^(100*k) / ballVol k 0 1) * (R^k)⁻¹
      * ∫ y in Metric.ball x R, W y) := by
    intro x
    rw [hW]
    exact mul_le_mul_of_nonneg_left (ballWeight_le_ball_average k hk c hR0 x) (hFnn x)
  -- integrability of the dominating function
  have hIntR : Integrable (fun x : E k => F x * (((2:ℝ)^(100*k) / ballVol k 0 1) * (R^k)⁻¹
      * ∫ y in Metric.ball x R, W y)) volume := by
    refine Integrable.mono' (hWint.const_mul (M ^ Q * (((2:ℝ)^(100*k) / ballVol k 0 1)
      * (R^k)⁻¹ * ((2:ℝ)^(200*k) * (R^k * ballVol k 0 1))))) ?_ ?_
    · refine ((hFm.mul (measurable_const.mul (measurable_ballAverage k W hWm R)))).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun x => ?_
      rw [Real.norm_of_nonneg (mul_nonneg (hFnn x) (mul_nonneg (by positivity)
        (integral_nonneg (fun y => hWnn y))))]
      have h2 := hKW x
      have h3 : F x * (((2:ℝ)^(100*k) / ballVol k 0 1) * (R^k)⁻¹ * ∫ y in Metric.ball x R, W y)
          ≤ M ^ Q * (((2:ℝ)^(100*k) / ballVol k 0 1) * (R^k)⁻¹ * ∫ y in Metric.ball x R, W y) :=
        mul_le_mul_of_nonneg_right (hFbound x)
          (mul_nonneg (by positivity) (integral_nonneg (fun y => hWnn y)))
      have h4 : M ^ Q * (((2:ℝ)^(100*k) / ballVol k 0 1) * (R^k)⁻¹
            * ∫ y in Metric.ball x R, W y)
          ≤ M ^ Q * (((2:ℝ)^(100*k) / ballVol k 0 1) * (R^k)⁻¹
            * (((2:ℝ)^(200*k) * (R^k * ballVol k 0 1)) * W x)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (by positivity))
          (Real.rpow_nonneg (by linarith) Q)
      calc F x * (((2:ℝ)^(100*k) / ballVol k 0 1) * (R^k)⁻¹ * ∫ y in Metric.ball x R, W y)
          ≤ M ^ Q * (((2:ℝ)^(100*k) / ballVol k 0 1) * (R^k)⁻¹
            * (((2:ℝ)^(200*k) * (R^k * ballVol k 0 1)) * W x)) := le_trans h3 h4
        _ = M ^ Q * (((2:ℝ)^(100*k) / ballVol k 0 1) * (R^k)⁻¹
            * ((2:ℝ)^(200*k) * (R^k * ballVol k 0 1))) * W x := by ring
  calc ∫ x : E k, F x * W x
      ≤ ∫ x : E k, F x * (((2:ℝ)^(100*k) / ballVol k 0 1) * (R^k)⁻¹
          * ∫ y in Metric.ball x R, W y) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => mul_nonneg (hFnn x) (hWnn x)))
          hIntR (Filter.Eventually.of_forall hpt)
    _ = (((2:ℝ)^(100*k) / ballVol k 0 1) * (R^k)⁻¹)
          * ∫ x : E k, F x * (∫ y in Metric.ball x R, W y) := by
        rw [← integral_const_mul]
        exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    _ = (((2:ℝ)^(100*k) / ballVol k 0 1) * (R^k)⁻¹)
          * ∫ c' : E k, W c' * (∫ x in Metric.ball c' R, F x) := by rw [hswap]
    _ = (((2:ℝ)^(100*k) / ballVol k 0 1) * (R^k)⁻¹)
          * ∫ c' : E k, ballWeight k c R c' * (∫ x in Metric.ball c' R, ‖extOp k g 0 1 x‖ ^ Q) := by
        rw [hW, hF]

/-- The localizing weight is dominated by the ball weight:
`‖φ_{B(c,R)}(y)‖^p ≲ w_B(y)` for `p ≥ 1` (Schwartz decay of `𝓕⁻(freqBump)`). -/
lemma phiB_le_ballWeight (k : ℕ) {P : ℝ} (hP : 1 ≤ P) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : E k) {R : ℝ}, 0 < R → ∀ y : E k,
      ‖phiB k c R y‖ ^ P ≤ C * ballWeight k c R y := by
  obtain ⟨C, hCpos, hC⟩ := schwartz_decay_rpow (k := k) hP
  refine ⟨C, hCpos, fun c R hR y => ?_⟩
  rw [phiB_eq_schwartz, ballWeight_eq_rpow k c hR y]
  refine (hC ((R⁻¹:ℝ) • (y - c))).trans (le_of_eq ?_)
  congr 2
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hR.le), inv_mul_eq_div]

/-- **Ball-local `L^q`–`L^p` comparison with the decaying ball weight**
(the "inside-the-ball" half of BDG's §7 Corollary):
`∫_{B(c,R)} ‖E_{[0,1]}g‖^q ≲ (∫ ‖E_{[0,1]}g‖^p w_B)^{q/p}` for `R ≥ 1`, `q ≥ p > 1`,
with a constant independent of `c`, `R`, `g`. -/
lemma extOp_ball_Lq_le_wB (k : ℕ) (hk : 1 ≤ k) (g : ℝ → ℂ)
    (hg : IntegrableOn g (Set.Icc (0:ℝ) 1) volume)
    {P Q : ℝ} (hP : 1 < P) (hPQ : P ≤ Q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : E k) {R : ℝ}, 1 ≤ R →
      ∫ x in Metric.ball c R, ‖extOp k g 0 1 x‖ ^ Q
        ≤ C * (∫ y, ‖extOp k g 0 1 y‖ ^ P * ballWeight k c R y) ^ (Q / P) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := phiB_le_ballWeight (k := k) (P := P) hP.le
  set M₁ : ℝ := (phiBMass k) ^ (-Q)
      * ((((∫ y, ‖(reproKernel k : E k → ℂ) y‖ ^ (P / (P - 1))) ^ ((P - 1) / P))
          ^ (1 - P/Q)) ^ Q) with hM₁
  refine ⟨max 1 (M₁ * C₁ ^ (Q/P)), ?_, ?_⟩
  · exact lt_of_lt_of_le one_pos (le_max_left _ _)
  · intro c R hR
    have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
    have hQ0 : 0 ≤ Q := by linarith
    have hP0 : 0 < P := lt_trans zero_lt_one hP
    -- the inside-ball bound
    have hmain := extOp_ball_Lq_le k g hg c hR hPQ hP
      ((Real.holderConjugate_iff_eq_conjExponent hP).mpr rfl)
    -- comparison of the `φ`-weighted integral with the ball weight
    have hcomp : (∫ y, ‖phiB k c R y * extOp k g 0 1 y‖ ^ P)
        ≤ C₁ * ∫ y, ‖extOp k g 0 1 y‖ ^ P * ballWeight k c R y := by
      have hpt : ∀ y : E k, ‖phiB k c R y * extOp k g 0 1 y‖ ^ P
          = ‖phiB k c R y‖ ^ P * ‖extOp k g 0 1 y‖ ^ P := by
        intro y
        rw [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
      have hInt2 : Integrable (fun y : E k => (C₁ * ballWeight k c R y)
          * ‖extOp k g 0 1 y‖ ^ P) volume := by
        refine Integrable.mono' ((ballWeight_integrable k hk c hR0).const_mul
          (C₁ * (∫ t in (0:ℝ)..1, ‖g t‖) ^ P)) ?_ ?_
        · exact ((continuous_const.mul (ballWeight_continuous k c hR0)).mul
            (((continuous_extOp k g hg).norm).rpow_const
              (fun y => Or.inr (by linarith)))).aestronglyMeasurable
        · refine Filter.Eventually.of_forall fun y => ?_
          rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg hC₁pos.le
            (le_of_lt (ballWeight_pos k c hR0 y))) (Real.rpow_nonneg (norm_nonneg _) P))]
          have hb : ‖extOp k g 0 1 y‖ ≤ ∫ t in (0:ℝ)..1, ‖g t‖ := by
            rw [extOp]
            calc ‖∫ t in (0:ℝ)..1, g t * momChar k y t‖
                ≤ ∫ t in (0:ℝ)..1, ‖g t * momChar k y t‖ :=
                  intervalIntegral.norm_integral_le_integral_norm (by norm_num)
              _ = ∫ t in (0:ℝ)..1, ‖g t‖ := by
                  refine intervalIntegral.integral_congr fun t _ => ?_
                  rw [norm_mul, momChar_norm_one, mul_one]
          have hp : ‖extOp k g 0 1 y‖ ^ P ≤ (∫ t in (0:ℝ)..1, ‖g t‖) ^ P :=
            Real.rpow_le_rpow (norm_nonneg _) hb (by linarith)
          calc C₁ * ballWeight k c R y * ‖extOp k g 0 1 y‖ ^ P
              ≤ C₁ * ballWeight k c R y * (∫ t in (0:ℝ)..1, ‖g t‖) ^ P :=
                mul_le_mul_of_nonneg_left hp
                  (mul_nonneg hC₁pos.le (le_of_lt (ballWeight_pos k c hR0 y)))
            _ = C₁ * (∫ t in (0:ℝ)..1, ‖g t‖) ^ P * ballWeight k c R y := by ring
      calc (∫ y, ‖phiB k c R y * extOp k g 0 1 y‖ ^ P)
          = ∫ y, ‖phiB k c R y‖ ^ P * ‖extOp k g 0 1 y‖ ^ P :=
            integral_congr_ae (Filter.Eventually.of_forall hpt)
        _ ≤ ∫ y, (C₁ * ballWeight k c R y) * ‖extOp k g 0 1 y‖ ^ P := by
            refine integral_mono_of_nonneg
              (Filter.Eventually.of_forall fun y => mul_nonneg
                (Real.rpow_nonneg (norm_nonneg _) P) (Real.rpow_nonneg (norm_nonneg _) P))
              hInt2 (Filter.Eventually.of_forall fun y => ?_)
            exact mul_le_mul_of_nonneg_right (hC₁ c hR0 y)
              (Real.rpow_nonneg (norm_nonneg _) P)
        _ = C₁ * ∫ y, ‖extOp k g 0 1 y‖ ^ P * ballWeight k c R y := by
            rw [← integral_const_mul]
            exact integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)
    -- combine
    have hstep : ∫ x in Metric.ball c R, ‖extOp k g 0 1 x‖ ^ Q
        ≤ M₁ * (∫ y, ‖phiB k c R y * extOp k g 0 1 y‖ ^ P) ^ (Q / P) := by
      rw [hM₁]
      refine hmain.trans (le_of_eq ?_)
      congr 2
      rw [one_div_div]
    have hB0 : 0 ≤ ∫ y, ‖extOp k g 0 1 y‖ ^ P * ballWeight k c R y :=
      integral_nonneg (fun y => mul_nonneg (Real.rpow_nonneg (norm_nonneg _) P)
        (le_of_lt (ballWeight_pos k c hR0 y)))
    have hle2 : (∫ y, ‖phiB k c R y * extOp k g 0 1 y‖ ^ P) ^ (Q / P)
        ≤ (C₁ * ∫ y, ‖extOp k g 0 1 y‖ ^ P * ballWeight k c R y) ^ (Q / P) :=
      Real.rpow_le_rpow (integral_nonneg (fun y => Real.rpow_nonneg (norm_nonneg _) P)) hcomp
        (div_nonneg hQ0 hP0.le)
    have hle3 : (C₁ * ∫ y, ‖extOp k g 0 1 y‖ ^ P * ballWeight k c R y) ^ (Q / P)
        = C₁ ^ (Q/P) * (∫ y, ‖extOp k g 0 1 y‖ ^ P * ballWeight k c R y) ^ (Q/P) :=
      Real.mul_rpow hC₁pos.le hB0
    calc ∫ x in Metric.ball c R, ‖extOp k g 0 1 x‖ ^ Q
        ≤ M₁ * (∫ y, ‖phiB k c R y * extOp k g 0 1 y‖ ^ P) ^ (Q / P) := hstep
      _ ≤ M₁ * (C₁ ^ (Q/P) * (∫ y, ‖extOp k g 0 1 y‖ ^ P * ballWeight k c R y) ^ (Q/P)) := by
          rw [hle3] at hle2
          exact mul_le_mul_of_nonneg_left hle2 (by
            rw [hM₁]
            have h1 : 0 ≤ ((∫ y, ‖(reproKernel k : E k → ℂ) y‖ ^ (P / (P - 1))) ^ ((P - 1) / P)) ^ (1 - P/Q) :=
              Real.rpow_nonneg (Real.rpow_nonneg (integral_nonneg (fun y =>
                Real.rpow_nonneg (norm_nonneg _) _)) _) _
            have h2 : 0 ≤ (phiBMass k) ^ (-Q) := Real.rpow_nonneg (le_of_lt (phiBMass_pos k)) _
            have h3 : 0 ≤ ((((∫ y, ‖(reproKernel k : E k → ℂ) y‖ ^ (P / (P - 1))) ^ ((P - 1) / P))
                ^ (1 - P/Q)) ^ Q) := Real.rpow_nonneg h1 _
            positivity)
      _ = (M₁ * C₁ ^ (Q/P)) * (∫ y, ‖extOp k g 0 1 y‖ ^ P * ballWeight k c R y) ^ (Q/P) := by
          ring
      _ ≤ max 1 (M₁ * C₁ ^ (Q/P))
            * (∫ y, ‖extOp k g 0 1 y‖ ^ P * ballWeight k c R y) ^ (Q/P) := by
          refine mul_le_mul_of_nonneg_right (le_max_right _ _)
            (Real.rpow_nonneg hB0 _)

end Submission.Vinogradov
