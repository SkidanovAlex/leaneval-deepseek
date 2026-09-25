/-
# Uniform (in the function) Schauder estimates for the Beurling transform

`Work.Beltrami.beurling_bounded` and `Work.Beltrami.beurling_holder_difference` prove the
pointwise and the Hölder (Calderón--Zygmund) estimate for the Beurling transform, but their
statements only expose *some* positive constant, so as stated the constant may depend on the
function `f`, its size `M`, its Hölder constant `K` and its support radius `R`.

This file records the two estimates with the constants made explicit.  In the source proofs the
constants are already independent of `f, M, K, R`: the pointwise bound uses `2/α + 10`, and the
Hölder bound uses
`max (12π/α + 72π + (12π·2^(α-1)/(1-α) + C₃ + 12 + π)) (2·(2/α+10)) + 1`,
where `C₃` is the absolute constant of `Work.Beltrami.Holder.W_translate_L1_bound`.
Hence both estimates are uniform in the function, and the target theorem
`Work.Beltrami.beurling_holder_uniform` follows.
-/
import Mathlib
import Submission.Work.Beltrami.Cauchy
import Submission.Work.Beltrami.beurling_bounded
import Submission.Work.Beltrami.beurling_holder_difference

noncomputable section

open MeasureTheory Set
open scoped Topology ContDiff

namespace Work.Beltrami

open Work.Beltrami

/-- **Uniform pointwise bound for the Beurling transform with an explicit constant.**
For `f` bounded by `M`, `α`-Hölder with constant `K` (`0 < α < 1`) and supported in the ball of
radius `R`, `‖beurling f z‖ ≤ (2/α + 10) (M + K) (1 + R)` for every `z`.  This is
`Work.Beltrami.beurling_bounded` with its constant made explicit. -/
theorem beurling_bounded_uniform {α M K R : ℝ} (hα : 0 < α) (hα1 : α < 1) (hR : 0 ≤ R)
    (f : ℂ → ℂ) (hM : ∀ z, ‖f z‖ ≤ M) (hK : ∀ x y : ℂ, ‖f x - f y‖ ≤ K * ‖x - y‖ ^ α)
    (hsupp : ∀ z, R < ‖z‖ → f z = 0) :
    ∀ z, ‖beurling f z‖ ≤ (2 / α + 10) * (M + K) * (1 + R) := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg (f 0)) (hM 0)
  have hK0 : 0 ≤ K := by
    have h := hK 0 1
    rw [show (0:ℂ) - 1 = -(1:ℂ) from by ring, norm_neg, norm_one, Real.one_rpow, mul_one] at h
    linarith [norm_nonneg (f 0 - f 1)]
  have hαne : α ≠ 0 := ne_of_gt hα
  have hαne2 : α ≠ 2 := by intro hc; rw [hc] at hα1; norm_num at hα1
  intro z
  rw [beurling_eq_translate]
  set F : ℂ → ℂ := fun w => (f (z + w) - (bumpC w : ℂ) * f z) * (w ^ 2)⁻¹ with hF
  set A : Set ℂ := {w : ℂ | 1 ≤ ‖w‖ ∧ ‖z + w‖ < R + 1} with hAset
  let tf : ℂ → ℝ := fun w => K * ((Metric.ball (0:ℂ) 1).indicator (fun w => ‖w‖ ^ (α - 2)) w)
  let tg : ℂ → ℝ := fun w => 4 * M * ((Metric.ball (0:ℂ) 1).indicator (fun _ : ℂ => (1:ℝ)) w)
  let th : ℂ → ℝ := fun w => M * (‖w‖⁻¹ * A.indicator (fun _ => (1:ℝ)) w)
  let G : ℂ → ℝ := fun w => tf w + tg w + th w
  change ‖(-(Real.pi)⁻¹ : ℝ) • ∫ w, F w‖ ≤ (2 / α + 10) * (M + K) * (1 + R)
  have hAmeas : MeasurableSet A := by
    rw [hAset]
    exact (isClosed_le continuous_const continuous_norm).measurableSet.inter
      (isOpen_lt (continuous_norm.comp (continuous_const.add continuous_id))
        continuous_const).measurableSet
  -- the three majorising pieces
  have ht1 : Integrable tf := by
    have h : Integrable ((Metric.ball (0:ℂ) 1).indicator (fun w => ‖w‖ ^ (α - 2))) :=
      MeasureTheory.IntegrableOn.integrable_indicator
        (Work.CR.Flat.Cauchy.integrableOn_norm_rpow_ball (ρ := 1) (s := α - 2) (by linarith))
        Metric.isOpen_ball.measurableSet
    exact h.const_mul K
  have ht2 : Integrable tg := by
    have h : Integrable ((Metric.ball (0:ℂ) 1).indicator (fun _ : ℂ => (1:ℝ))) :=
      MeasureTheory.IntegrableOn.integrable_indicator
        (integrableOn_const (s := Metric.ball (0:ℂ) 1) measure_ball_lt_top.ne (by simp))
        Metric.isOpen_ball.measurableSet
    exact h.const_mul (4 * M)
  have ht3 : Integrable th := by
    have hJ : Integrable
        (fun w : ℂ => M * ((Metric.ball (-z) (R + 1)).indicator (fun w => ‖w‖⁻¹) w)) :=
      (integrable_indicator_norm_inv (-z) (R + 1)).const_mul M
    refine MeasureTheory.Integrable.mono' hJ ?_ ?_
    · apply AEMeasurable.aestronglyMeasurable
      apply Measurable.aemeasurable
      exact measurable_const.mul ((continuous_norm.measurable.inv).mul
        (Measurable.indicator measurable_const hAmeas))
    · filter_upwards with w
      have hthw : th w = M * (‖w‖⁻¹ * A.indicator (fun _ => (1:ℝ)) w) := rfl
      rw [hthw]
      by_cases hw : w ∈ A
      · have hwb : w ∈ Metric.ball (-z) (R + 1) := by
          rw [hAset] at hw
          rw [Metric.mem_ball, dist_eq_norm]
          rw [show w - -z = w + z from by ring, add_comm]
          exact hw.2
        rw [Set.indicator_of_mem hw, mul_one, Set.indicator_of_mem hwb]
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      · simp only [Set.indicator_of_notMem hw, mul_zero, norm_zero]
        exact mul_nonneg hM0 (Set.indicator_nonneg (fun a _ => inv_nonneg.mpr (norm_nonneg a)) w)
  have ht12 : Integrable (fun w : ℂ => tf w + tg w) := ht1.add ht2
  have hG_int : Integrable G := (ht1.add ht2).add ht3
  -- pointwise domination
  have hFG : ∀ w : ℂ, ‖F w‖ ≤ G w := by
    intro w
    have hFw : F w = (f (z + w) - (bumpC w : ℂ) * f z) * (w ^ 2)⁻¹ := rfl
    have hGw : G w = K * ((Metric.ball (0:ℂ) 1).indicator (fun w => ‖w‖ ^ (α - 2)) w)
        + 4 * M * ((Metric.ball (0:ℂ) 1).indicator (fun _ : ℂ => (1:ℝ)) w)
        + M * (‖w‖⁻¹ * A.indicator (fun _ => (1:ℝ)) w) := rfl
    rw [hFw, hGw]
    have hbump_le : ‖(1 : ℂ) - (bumpC w : ℂ)‖ ≤ 1 := by
      have hcast : (1 : ℂ) - (bumpC w : ℂ) = ((1 - bumpC w : ℝ) : ℂ) := by push_cast; ring
      rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [bumpC_le_one w], by linarith [bumpC_nonneg w]⟩
    rcases lt_or_ge (‖w‖) (1/2) with h2 | h2
    · -- `‖w‖ < 1/2`: the cutoff equals one and the subtraction is exact
      have hbump : bumpC w = 1 := bumpC_eq_one (le_of_lt h2)
      have hmem : w ∈ Metric.ball (0:ℂ) 1 := by
        rw [Metric.mem_ball, dist_eq_norm]; simp only [sub_zero]; linarith
      have hnotA : w ∉ A := by
        rw [hAset]; intro hc; exact absurd hc.1 (by linarith)
      have hG1 : K * ((Metric.ball (0:ℂ) 1).indicator (fun w => ‖w‖ ^ (α - 2)) w)
          + 4 * M * ((Metric.ball (0:ℂ) 1).indicator (fun _ : ℂ => (1:ℝ)) w)
          + M * (‖w‖⁻¹ * A.indicator (fun _ => (1:ℝ)) w) = K * ‖w‖ ^ (α - 2) + 4 * M := by
        simp only [Set.indicator_of_mem hmem, Set.indicator_of_notMem hnotA, mul_one, mul_zero,
          add_zero]
      rw [hG1]
      calc ‖(f (z + w) - (bumpC w : ℂ) * f z) * (w ^ 2)⁻¹‖
          = ‖(f (z + w) - f z) * (w ^ 2)⁻¹‖ := by
              rw [hbump, Complex.ofReal_one, one_mul]
        _ = ‖f (z + w) - f z‖ * (‖w‖ ^ 2)⁻¹ := by rw [norm_mul, norm_inv, norm_pow]
        _ ≤ K * ‖w‖ ^ α * (‖w‖ ^ 2)⁻¹ := by
              refine mul_le_mul_of_nonneg_right ?_ (by positivity)
              have h := hK (z + w) z
              rwa [add_sub_cancel_left] at h
        _ = K * ‖w‖ ^ (α - 2) := by
              rw [mul_assoc, rpow_mul_inv_sq hαne hαne2 ‖w‖ (norm_nonneg w)]
        _ ≤ K * ‖w‖ ^ (α - 2) + 4 * M := le_add_of_nonneg_right (by positivity)
    · rcases lt_or_ge (‖w‖) 1 with h1 | h1
      · -- `1/2 ≤ ‖w‖ < 1`: the cutoff is bounded by one
        have hmem : w ∈ Metric.ball (0:ℂ) 1 := by
          rw [Metric.mem_ball, dist_eq_norm]; simp only [sub_zero]; exact h1
        have hnotA : w ∉ A := by
          rw [hAset]; intro hc; exact absurd hc.1 (by linarith)
        have hG1 : K * ((Metric.ball (0:ℂ) 1).indicator (fun w => ‖w‖ ^ (α - 2)) w)
            + 4 * M * ((Metric.ball (0:ℂ) 1).indicator (fun _ : ℂ => (1:ℝ)) w)
            + M * (‖w‖⁻¹ * A.indicator (fun _ => (1:ℝ)) w) = K * ‖w‖ ^ (α - 2) + 4 * M := by
          simp only [Set.indicator_of_mem hmem, Set.indicator_of_notMem hnotA, mul_one, mul_zero,
            add_zero]
        rw [hG1]
        have h4 : (‖w‖ ^ 2)⁻¹ ≤ 4 := by
          rw [inv_le_comm₀ (by positivity) (by norm_num : (0:ℝ) < 4)]
          norm_num
          nlinarith [norm_nonneg w]
        have hinner : ‖f (z + w) - (bumpC w : ℂ) * f z‖ ≤ K * ‖w‖ ^ α + M := by
          have hsub : f (z + w) - (bumpC w : ℂ) * f z
              = (f (z + w) - f z) + ((1 : ℂ) - (bumpC w : ℂ)) * f z := by ring
          rw [hsub]
          refine le_trans (norm_add_le _ _) ?_
          have h3 : ‖f (z + w) - f z‖ ≤ K * ‖w‖ ^ α := by
            have h := hK (z + w) z; rwa [add_sub_cancel_left] at h
          have h5 : ‖((1 : ℂ) - (bumpC w : ℂ)) * f z‖ ≤ 1 * M := by
            rw [norm_mul]
            exact mul_le_mul hbump_le (hM z) (norm_nonneg _) (by norm_num)
          linarith
        calc ‖(f (z + w) - (bumpC w : ℂ) * f z) * (w ^ 2)⁻¹‖
            = ‖f (z + w) - (bumpC w : ℂ) * f z‖ * (‖w‖ ^ 2)⁻¹ := by
                rw [norm_mul, norm_inv, norm_pow]
          _ ≤ (K * ‖w‖ ^ α + M) * (‖w‖ ^ 2)⁻¹ :=
                mul_le_mul_of_nonneg_right hinner (by positivity)
          _ = K * ‖w‖ ^ (α - 2) + M * (‖w‖ ^ 2)⁻¹ := by
                rw [add_mul, mul_assoc, rpow_mul_inv_sq hαne hαne2 ‖w‖ (norm_nonneg w)]
          _ ≤ K * ‖w‖ ^ (α - 2) + 4 * M := by
                linarith [mul_le_mul_of_nonneg_left h4 hM0]
      · -- `1 ≤ ‖w‖`: the cutoff vanishes, only the support of `f` contributes
        have hbc : bumpC w = 0 := bumpC_eq_zero h1
        have hnotmem : w ∉ Metric.ball (0:ℂ) 1 := by
          rw [Metric.mem_ball, dist_eq_norm]; simp only [sub_zero]; linarith
        have hG2 : K * ((Metric.ball (0:ℂ) 1).indicator (fun w => ‖w‖ ^ (α - 2)) w)
            + 4 * M * ((Metric.ball (0:ℂ) 1).indicator (fun _ : ℂ => (1:ℝ)) w)
            + M * (‖w‖⁻¹ * A.indicator (fun _ => (1:ℝ)) w)
            = M * (‖w‖⁻¹ * A.indicator (fun _ => (1:ℝ)) w) := by
          simp only [Set.indicator_of_notMem hnotmem, mul_zero, add_zero, zero_add]
        rw [hG2]
        by_cases hwA : w ∈ A
        · rw [Set.indicator_of_mem hwA, mul_one]
          have hinv : (‖w‖ ^ 2)⁻¹ ≤ ‖w‖⁻¹ := by
            rw [inv_le_inv₀ (by positivity) (by linarith)]
            nlinarith [norm_nonneg w]
          calc ‖(f (z + w) - (bumpC w : ℂ) * f z) * (w ^ 2)⁻¹‖
              = ‖f (z + w) - (bumpC w : ℂ) * f z‖ * (‖w‖ ^ 2)⁻¹ := by
                  rw [norm_mul, norm_inv, norm_pow]
            _ ≤ M * (‖w‖ ^ 2)⁻¹ := by
                  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
                  rw [show f (z + w) - (bumpC w : ℂ) * f z = f (z + w) from by
                    rw [hbc, Complex.ofReal_zero, zero_mul, sub_zero]]
                  exact hM (z + w)
            _ ≤ M * ‖w‖⁻¹ := mul_le_mul_of_nonneg_left hinv hM0
        · rw [Set.indicator_of_notMem hwA, mul_zero, mul_zero]
          have hzR : R < ‖z + w‖ := by
            by_contra hcon
            exact hwA (by rw [hAset]; exact ⟨h1, by linarith [(not_lt.mp hcon)]⟩)
          have hf0 : f (z + w) = 0 := hsupp (z + w) hzR
          simp only [hf0, hbc, Complex.ofReal_zero, zero_mul, sub_zero, norm_zero]
          exact le_refl 0
  -- value of the majorant
  have hG_val : ∫ w : ℂ, G w ≤
      2 * Real.pi * K / α + 4 * Real.pi * M + 6 * Real.pi * M * (1 + R) := by
    have hsplit : ∫ w : ℂ, G w = (∫ w, tf w) + (∫ w, tg w) + (∫ w, th w) := by
      rw [show (∫ w : ℂ, G w) = ∫ w : ℂ, (tf w + tg w + th w) from rfl]
      rw [integral_add ht12 ht3, integral_add ht1 ht2]
    rw [hsplit]
    have hv1 : ∫ w : ℂ, tf w = 2 * Real.pi * K / α := by
      rw [show (∫ w : ℂ, tf w) = ∫ w : ℂ,
        K * ((Metric.ball (0:ℂ) 1).indicator (fun w => ‖w‖ ^ (α - 2)) w) from rfl]
      rw [integral_const_mul, integral_indicator Metric.isOpen_ball.measurableSet,
        Work.CR.Flat.Cauchy.integral_norm_rpow_ball (ρ := 1) (s := α - 2)
          (by norm_num) (by linarith)]
      rw [Real.one_rpow, show α - 2 + 2 = α from by ring, mul_one, ← mul_div_assoc]
      congr 1
      ring
    have hv2 : ∫ w : ℂ, tg w = 4 * Real.pi * M := by
      rw [show (∫ w : ℂ, tg w) = ∫ w : ℂ,
        4 * M * ((Metric.ball (0:ℂ) 1).indicator (fun _ : ℂ => (1:ℝ)) w) from rfl]
      rw [integral_const_mul, integral_indicator_const (1:ℝ) Metric.isOpen_ball.measurableSet,
        volume_real_ball_one, smul_eq_mul]
      ring
    have hv3 : ∫ w : ℂ, th w ≤ 6 * Real.pi * M * (1 + R) := by
      rw [show (∫ w : ℂ, th w) = ∫ w : ℂ,
        M * (‖w‖⁻¹ * A.indicator (fun _ => (1:ℝ)) w) from rfl]
      have hJ : Integrable
          (fun w : ℂ => M * ((Metric.ball (-z) (R + 1)).indicator (fun w => ‖w‖⁻¹) w)) :=
        (integrable_indicator_norm_inv (-z) (R + 1)).const_mul M
      have hle : ∀ w : ℂ, M * (‖w‖⁻¹ * A.indicator (fun _ => (1:ℝ)) w)
          ≤ M * ((Metric.ball (-z) (R + 1)).indicator (fun w => ‖w‖⁻¹) w) := by
        intro w
        by_cases hw : w ∈ A
        · have hwb : w ∈ Metric.ball (-z) (R + 1) := by
            rw [hAset] at hw
            rw [Metric.mem_ball, dist_eq_norm]
            rw [show w - -z = w + z from by ring, add_comm]
            exact hw.2
          rw [Set.indicator_of_mem hw, mul_one, Set.indicator_of_mem hwb]
        · rw [Set.indicator_of_notMem hw, mul_zero, mul_zero]
          exact mul_nonneg hM0 (Set.indicator_nonneg (fun a _ => inv_nonneg.mpr (norm_nonneg a)) w)
      have hmono := integral_mono_of_nonneg
        (Filter.Eventually.of_forall (fun w : ℂ => mul_nonneg hM0
          (mul_nonneg (inv_nonneg.mpr (norm_nonneg w))
            (Set.indicator_nonneg (fun a _ => by norm_num) w))))
        hJ (Filter.Eventually.of_forall hle)
      have hJ2 : ∫ (a : ℂ), M * (Metric.ball (-z) (R + 1)).indicator (fun w => ‖w‖⁻¹) a
          = M * ∫ a in Metric.ball (-z) (R + 1), ‖a‖⁻¹ := by
        rw [integral_const_mul, integral_indicator Metric.isOpen_ball.measurableSet]
      rw [hJ2] at hmono
      have hb := integral_ball_norm_inv_le (-z) (R + 1) (by linarith)
      have hbound : M * (∫ w in Metric.ball (-z) (R + 1), ‖w‖⁻¹)
          ≤ 6 * Real.pi * M * (1 + R) := by
        have h4 : (1 + (R + 1)) ≤ 2 * (1 + R) := by linarith
        calc M * (∫ w in Metric.ball (-z) (R + 1), ‖w‖⁻¹)
            ≤ M * (3 * Real.pi * (1 + (R + 1))) := mul_le_mul_of_nonneg_left hb hM0
          _ ≤ M * (3 * Real.pi * (2 * (1 + R))) := by
                refine mul_le_mul_of_nonneg_left ?_ hM0
                nlinarith [Real.pi_pos, h4]
          _ = 6 * Real.pi * M * (1 + R) := by ring
      linarith [hmono, hbound]
    linarith [hv1, hv2, hv3]
  have hmain : ‖∫ w, F w‖ ≤ ∫ w : ℂ, G w := by
    refine le_trans (norm_integral_le_integral_norm F) ?_
    exact integral_mono_of_nonneg (Filter.Eventually.of_forall fun w => norm_nonneg _) hG_int
      (Filter.Eventually.of_forall hFG)
  have hnorm : ‖(-(Real.pi)⁻¹ : ℝ) • ∫ w, F w‖ = Real.pi⁻¹ * ‖∫ w, F w‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_neg,
      abs_of_nonneg (inv_nonneg.mpr Real.pi_pos.le)]
  have harith : Real.pi⁻¹ * (2 * Real.pi * K / α + 4 * Real.pi * M + 6 * Real.pi * M * (1 + R))
      = 2 * K / α + 4 * M + 6 * M * (1 + R) := by
    field_simp
  calc ‖(-(Real.pi)⁻¹ : ℝ) • ∫ w, F w‖
      = Real.pi⁻¹ * ‖∫ w, F w‖ := hnorm
    _ ≤ Real.pi⁻¹ * ∫ w : ℂ, G w := mul_le_mul_of_nonneg_left hmain (by positivity)
    _ ≤ Real.pi⁻¹ * (2 * Real.pi * K / α + 4 * Real.pi * M + 6 * Real.pi * M * (1 + R)) :=
        mul_le_mul_of_nonneg_left hG_val (by positivity)
    _ = 2 * K / α + 4 * M + 6 * M * (1 + R) := harith
    _ ≤ (2 / α + 10) * (M + K) * (1 + R) := by
        have hαinv : (0:ℝ) < 2/α := by positivity
        have h1R : (1:ℝ) ≤ 1 + R := by linarith
        have h2Ka : 2 * K / α = (2/α) * K := by ring
        rw [h2Ka]
        nlinarith [hM0, hK0, hR, hαinv, h1R, mul_nonneg hM0 hK0, mul_nonneg hM0 hR,
          mul_nonneg hK0 hR, mul_nonneg hαinv.le hM0, mul_nonneg hαinv.le hK0,
          mul_nonneg (mul_nonneg hM0 hK0) hR]

/-- **Hölder estimate for the Beurling transform with an explicit constant.**
For `f` bounded by `M`, `α`-Hölder with constant `K` (`0 < α < 1`) and supported in the ball of
radius `R`, the Beurling transform is `α`-Hölder with the explicit constant
`max (12π/α + 72π + (12π·2^(α-1)/(1-α) + C₃ + 12 + π)) (2·(2/α+10)) + 1`, where `C₃` is the
(universal) constant of `Work.Beltrami.Holder.W_translate_L1_bound`.  This is
`Work.Beltrami.beurling_holder_difference` with its constant made explicit and with the
pointwise estimate imported from `beurling_bounded_uniform`. -/
theorem beurling_holder_diff_bound {α M K R : ℝ} (hα : 0 < α) (hα1 : α < 1) (hR : 0 ≤ R)
    (f : ℂ → ℂ) (hM : ∀ z, ‖f z‖ ≤ M) (hK : ∀ x y : ℂ, ‖f x - f y‖ ≤ K * ‖x - y‖ ^ α)
    (hsupp : ∀ z, R < ‖z‖ → f z = 0) {C₃ : ℝ}
    (hC₃ : ∀ x y : ℂ, Integrable (fun u : ℂ => W (u - x) - W (u - y)) volume ∧
      (∫ u : ℂ, ‖W (u - x) - W (u - y)‖) ≤ C₃ * ‖x - y‖)
    (hC₃pos : 0 < C₃) :
    ∀ x y : ℂ, ‖beurling f x - beurling f y‖
      ≤ (max ((12 * Real.pi / α + 72 * Real.pi) + (12 * Real.pi * 2 ^ (α - 1) / (1 - α) + C₃ + 12 + Real.pi)) (2 * (2 / α + 10)) + 1) * (M + K) * (1 + R) * ‖x - y‖ ^ α := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg (f 0)) (hM 0)
  have hK0 : 0 ≤ K := by
    have h := hK 0 1
    rw [show (0 : ℂ) - 1 = -(1 : ℂ) from by ring, norm_neg, norm_one, Real.one_rpow,
      mul_one] at h
    linarith [norm_nonneg (f 0 - f 1)]
  -- the three analytic ingredients
  have hC₂ : ∀ z, ‖beurling f z‖ ≤ (2 / α + 10) * (M + K) * (1 + R) :=
    beurling_bounded_uniform hα hα1 hR f hM hK hsupp
  have hC₁ : ∀ z : ℂ, ∀ ρ : ℝ, 0 < ρ →
      ∫ ζ in Metric.ball z ρ,
          ‖(f ζ - (bumpC (ζ - z) : ℂ) * f z) * ((ζ - z) ^ 2)⁻¹‖ ∂volume
        ≤ 2 * Real.pi * K * ρ ^ α / α + 4 * Real.pi * M * ρ ^ 2 :=
    fun z ρ hρ => integral_ball_norm_bI_le (α := α) (K := K) (M := M) hα hK0 hM0 hM hK z hρ
  intro x y
  by_cases hxy : x = y
  · subst hxy
    have hzero : ‖x - x‖ ^ α = 0 := by
      rw [sub_self, norm_zero, Real.zero_rpow (ne_of_gt hα)]
    rw [sub_self, norm_zero, hzero, mul_zero]
  by_cases hδle : ‖x - y‖ ≤ 1
  · -- ================= main case: `δ ≤ 1` =================
    set δ : ℝ := ‖x - y‖ with hδdef
    have hδpos : 0 < δ := by
      rw [hδdef]
      exact norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    have hδle1 : δ ≤ 1 := by rw [hδdef]; exact hδle
    have hδpowpos : 0 < δ ^ α := Real.rpow_pos_of_pos hδpos α
    have hδsq_le : δ ^ 2 ≤ δ ^ α := by
      have h1 : δ ≤ δ ^ α := by
        have h2 : δ ^ (1 : ℝ) ≤ δ ^ α :=
          Real.rpow_le_rpow_of_exponent_ge hδpos hδle1 hα1.le
        rwa [Real.rpow_one] at h2
      have h3 : δ ^ 2 ≤ δ := by nlinarith [hδpos, hδle1]
      linarith
    -- the two integrands
    set Ix : ℂ → ℂ := fun ζ => (f ζ - (bumpC (ζ - x) : ℂ) * f x) * ((ζ - x) ^ 2)⁻¹ with hIx
    set Iy : ℂ → ℂ := fun ζ => (f ζ - (bumpC (ζ - y) : ℂ) * f y) * ((ζ - y) ^ 2)⁻¹ with hIy
    have hIntIx : Integrable Ix volume := by
      rw [hIx]; exact integrable_bI hα hK0 hM0 hM hK hsupp x
    have hIntIy : Integrable Iy volume := by
      rw [hIy]; exact integrable_bI hα hK0 hM0 hM hK hsupp y
    have hbeur : ‖beurling f x - beurling f y‖
        = Real.pi⁻¹ * ‖(∫ ζ, Ix ζ ∂volume) - (∫ ζ, Iy ζ ∂volume)‖ := by
      have h1 : beurling f x - beurling f y
          = (-(Real.pi)⁻¹ : ℝ) • ((∫ ζ, Ix ζ ∂volume) - (∫ ζ, Iy ζ ∂volume)) := by
        rw [beurling_apply, beurling_apply, ← hIx, ← hIy, smul_sub]
      rw [h1, norm_smul]
      congr 1
      rw [Real.norm_eq_abs, abs_neg, abs_inv, abs_of_nonneg Real.pi_pos.le]
    -- the regions
    set S : Set ℂ := Metric.ball x (2 * δ) ∪ Metric.ball y (2 * δ) with hS
    have hSmeas : MeasurableSet S := by
      rw [hS]; exact measurableSet_ball.union measurableSet_ball
    have hspos : (0 : ℝ) < 2 * δ := by linarith
    have hSx : S ⊆ Metric.ball x (3 * δ) := by
      intro ζ hζ
      rw [hS] at hζ
      rw [Metric.mem_ball]
      rcases hζ with h | h
      · rw [Metric.mem_ball] at h; linarith
      · rw [Metric.mem_ball] at h
        rw [dist_eq_norm] at h ⊢
        have h1 : ‖ζ - x‖ ≤ ‖ζ - y‖ + ‖y - x‖ := by
          rw [show ζ - x = (ζ - y) + (y - x) from by ring]
          exact norm_add_le _ _
        rw [show ‖y - x‖ = δ from by rw [norm_sub_rev, ← hδdef]] at h1
        linarith
    have hSy : S ⊆ Metric.ball y (3 * δ) := by
      intro ζ hζ
      rw [hS] at hζ
      rw [Metric.mem_ball]
      rcases hζ with h | h
      · rw [Metric.mem_ball] at h
        rw [dist_eq_norm] at h ⊢
        have h1 : ‖ζ - y‖ ≤ ‖ζ - x‖ + ‖x - y‖ := by
          rw [show ζ - y = (ζ - x) + (x - y) from by ring]
          exact norm_add_le _ _
        rw [show ‖x - y‖ = δ from hδdef.symm] at h1
        linarith
      · rw [Metric.mem_ball] at h; linarith
    -- splitting of the integral
    have hsplit : (∫ ζ, Ix ζ ∂volume) - (∫ ζ, Iy ζ ∂volume)
        = (∫ ζ in S, (Ix ζ - Iy ζ) ∂volume) + (∫ ζ in Sᶜ, (Ix ζ - Iy ζ) ∂volume) := by
      have h1 : (∫ ζ, Ix ζ ∂volume) - (∫ ζ, Iy ζ ∂volume) = ∫ ζ, (Ix ζ - Iy ζ) ∂volume :=
        (integral_sub hIntIx hIntIy).symm
      rw [h1]
      exact (integral_add_compl hSmeas (hIntIx.sub hIntIy)).symm
    -- ===== near part =====
    have hnear : ‖∫ ζ in S, (Ix ζ - Iy ζ) ∂volume‖ ≤ (12 * Real.pi / α + 72 * Real.pi) * (M + K) * δ ^ α := by
      have h1 : ‖∫ ζ in S, (Ix ζ - Iy ζ) ∂volume‖ ≤ ∫ ζ in S, ‖Ix ζ - Iy ζ‖ ∂volume :=
        norm_integral_le_integral_norm _
      have h2 : ∫ ζ in S, ‖Ix ζ - Iy ζ‖ ∂volume
          ≤ ∫ ζ in S, (‖Ix ζ‖ + ‖Iy ζ‖) ∂volume := by
        refine integral_mono (f := fun ζ => ‖Ix ζ - Iy ζ‖)
          (g := fun ζ => ‖Ix ζ‖ + ‖Iy ζ‖) (hIntIx.sub hIntIy).norm.integrableOn
          (hIntIx.norm.add hIntIy.norm).integrableOn ?_
        exact fun ζ => norm_sub_le (Ix ζ) (Iy ζ)
      have h3 : ∫ ζ in S, (‖Ix ζ‖ + ‖Iy ζ‖) ∂volume
          = (∫ ζ in S, ‖Ix ζ‖ ∂volume) + (∫ ζ in S, ‖Iy ζ‖ ∂volume) :=
        integral_add hIntIx.norm.integrableOn hIntIy.norm.integrableOn
      have h4 : ∫ ζ in S, ‖Ix ζ‖ ∂volume ≤ ∫ ζ in Metric.ball x (3 * δ), ‖Ix ζ‖ ∂volume :=
        setIntegral_mono_set hIntIx.norm.integrableOn
          (Filter.Eventually.of_forall fun ζ => norm_nonneg _)
          (Filter.Eventually.of_forall fun ζ hζ => hSx hζ)
      have h5 : ∫ ζ in S, ‖Iy ζ‖ ∂volume ≤ ∫ ζ in Metric.ball y (3 * δ), ‖Iy ζ‖ ∂volume :=
        setIntegral_mono_set hIntIy.norm.integrableOn
          (Filter.Eventually.of_forall fun ζ => norm_nonneg _)
          (Filter.Eventually.of_forall fun ζ hζ => hSy hζ)
      have h6 : ∫ ζ in Metric.ball x (3 * δ), ‖Ix ζ‖ ∂volume
          ≤ 2 * Real.pi * K * (3 * δ) ^ α / α + 4 * Real.pi * M * (3 * δ) ^ 2 := by
        have := hC₁ x (3 * δ) (by linarith)
        simpa only [hIx] using this
      have h7 : ∫ ζ in Metric.ball y (3 * δ), ‖Iy ζ‖ ∂volume
          ≤ 2 * Real.pi * K * (3 * δ) ^ α / α + 4 * Real.pi * M * (3 * δ) ^ 2 := by
        have := hC₁ y (3 * δ) (by linarith)
        simpa only [hIy] using this
      have h8 : 2 * Real.pi * K * (3 * δ) ^ α / α + 4 * Real.pi * M * (3 * δ) ^ 2
          + (2 * Real.pi * K * (3 * δ) ^ α / α + 4 * Real.pi * M * (3 * δ) ^ 2)
          ≤ (12 * Real.pi / α + 72 * Real.pi) * (M + K) * δ ^ α := by
        have hmul : (3 * δ) ^ α = 3 ^ α * δ ^ α := Real.mul_rpow (by norm_num) hδpos.le
        have h32 : (3 * δ) ^ 2 = 9 * δ ^ 2 := by ring
        rw [hmul, h32]
        have h3a : (3 : ℝ) ^ α ≤ 3 := by
          simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3) hα1.le
        have hA : 2 * Real.pi * K * (3 ^ α * δ ^ α) / α ≤ 6 * Real.pi * K * δ ^ α / α := by
          have hcoef : (0:ℝ) ≤ 2 * Real.pi * K * δ ^ α / α := by positivity
          have h1 : 2 * Real.pi * K * (3 ^ α * δ ^ α) / α
              = (2 * Real.pi * K * δ ^ α / α) * 3 ^ α := by
            rw [div_eq_mul_inv]; ring
          have h2 : (2 * Real.pi * K * δ ^ α / α) * 3 = 6 * Real.pi * K * δ ^ α / α := by
            rw [div_eq_mul_inv]; ring
          rw [h1, ← h2]
          exact mul_le_mul_of_nonneg_left h3a hcoef
        have hB : 4 * Real.pi * M * (9 * δ ^ 2) ≤ 36 * Real.pi * M * δ ^ α := by
          have hcoef : (0:ℝ) ≤ 4 * Real.pi * M * 9 := by positivity
          have h1 : 4 * Real.pi * M * (9 * δ ^ 2) = (4 * Real.pi * M * 9) * δ ^ 2 := by ring
          have h2 : (4 * Real.pi * M * 9) * δ ^ α = 36 * Real.pi * M * δ ^ α := by ring
          rw [h1, ← h2]
          exact mul_le_mul_of_nonneg_left hδsq_le hcoef
        have hfin : 12 * Real.pi * K * δ ^ α / α + 72 * Real.pi * M * δ ^ α
            ≤ (12 * Real.pi / α + 72 * Real.pi) * (M + K) * δ ^ α := by
          have hK' : K ≤ M + K := by linarith
          have hM' : M ≤ M + K := by linarith
          have h1 : 12 * Real.pi * K * δ ^ α / α ≤ 12 * Real.pi * (M + K) * δ ^ α / α := by
            have hcoef : (0:ℝ) < 12 * Real.pi * δ ^ α / α := by positivity
            have h3 : 12 * Real.pi * K * δ ^ α / α
                = (12 * Real.pi * δ ^ α / α) * K := by rw [div_eq_mul_inv]; ring
            have h4 : 12 * Real.pi * (M + K) * δ ^ α / α
                = (12 * Real.pi * δ ^ α / α) * (M + K) := by rw [div_eq_mul_inv]; ring
            rw [h3, h4]
            exact mul_le_mul_of_nonneg_left hK' hcoef.le
          have h2 : 72 * Real.pi * M * δ ^ α ≤ 72 * Real.pi * (M + K) * δ ^ α := by
            have hcoef : (0:ℝ) ≤ 72 * Real.pi * δ ^ α := by positivity
            have h3 : 72 * Real.pi * M * δ ^ α = (72 * Real.pi * δ ^ α) * M := by ring
            have h4 : 72 * Real.pi * (M + K) * δ ^ α = (72 * Real.pi * δ ^ α) * (M + K) := by ring
            rw [h3, h4]
            exact mul_le_mul_of_nonneg_left hM' hcoef
          have h3 : 12 * Real.pi * (M + K) * δ ^ α / α + 72 * Real.pi * (M + K) * δ ^ α
              = (12 * Real.pi / α + 72 * Real.pi) * (M + K) * δ ^ α := by
            rw [div_eq_mul_inv]; ring
          linarith
        calc 2 * Real.pi * K * (3 ^ α * δ ^ α) / α + 4 * Real.pi * M * (9 * δ ^ 2)
              + (2 * Real.pi * K * (3 ^ α * δ ^ α) / α + 4 * Real.pi * M * (9 * δ ^ 2))
            ≤ 2 * (6 * Real.pi * K * δ ^ α / α + 36 * Real.pi * M * δ ^ α) := by linarith [hA, hB]
          _ = 12 * Real.pi * K * δ ^ α / α + 72 * Real.pi * M * δ ^ α := by ring
          _ ≤ (12 * Real.pi / α + 72 * Real.pi) * (M + K) * δ ^ α := hfin
      calc ‖∫ ζ in S, (Ix ζ - Iy ζ) ∂volume‖
          ≤ ∫ ζ in S, ‖Ix ζ - Iy ζ‖ ∂volume := h1
        _ ≤ ∫ ζ in S, (‖Ix ζ‖ + ‖Iy ζ‖) ∂volume := h2
        _ = (∫ ζ in S, ‖Ix ζ‖ ∂volume) + (∫ ζ in S, ‖Iy ζ‖ ∂volume) := h3
        _ ≤ (∫ ζ in Metric.ball x (3 * δ), ‖Ix ζ‖ ∂volume)
              + (∫ ζ in Metric.ball y (3 * δ), ‖Iy ζ‖ ∂volume) := add_le_add h4 h5
        _ ≤ (2 * Real.pi * K * (3 * δ) ^ α / α + 4 * Real.pi * M * (3 * δ) ^ 2)
              + (2 * Real.pi * K * (3 * δ) ^ α / α + 4 * Real.pi * M * (3 * δ) ^ 2) :=
            add_le_add h6 h7
        _ ≤ (12 * Real.pi / α + 72 * Real.pi) * (M + K) * δ ^ α := h8
    -- ===== far part =====
    set T1 : ℂ → ℂ := fun ζ => (f ζ - f x) * (((ζ - x) ^ 2)⁻¹ - ((ζ - y) ^ 2)⁻¹) with hT1
    set T2 : ℂ → ℂ := fun ζ => f x * (W (ζ - x) - W (ζ - y)) with hT2
    set T3 : ℂ → ℂ := fun ζ => (f y - f x) * ((bumpC (ζ - y) : ℂ) * (((ζ - y) ^ 2)⁻¹)) with hT3
    have hdecomp : ∀ ζ ∈ Sᶜ, Ix ζ - Iy ζ = T1 ζ + T2 ζ + T3 ζ := by
      intro ζ hζ
      have hζx : ζ ≠ x := by
        intro h
        exact hζ (by rw [hS]; exact Or.inl (h ▸ Metric.mem_ball_self hspos))
      have hζy : ζ ≠ y := by
        intro h
        exact hζ (by rw [hS]; exact Or.inr (h ▸ Metric.mem_ball_self hspos))
      have ha : (ζ - x) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hζx)
      have hb : (ζ - y) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hζy)
      simp only [hIx, hIy, hT1, hT2, hT3, W_apply]
      field_simp
      ring
    have hcongr : ∫ ζ in Sᶜ, (Ix ζ - Iy ζ) ∂volume
        = ∫ ζ in Sᶜ, (T1 ζ + T2 ζ + T3 ζ) ∂volume :=
      setIntegral_congr_fun hSmeas.compl hdecomp
    have hsubx : Sᶜ ⊆ {ζ : ℂ | 2 * δ ≤ ‖ζ - x‖} := by
      intro ζ hζ
      have h1 : ζ ∉ Metric.ball x (2 * δ) := fun h => hζ (by rw [hS]; exact Or.inl h)
      rwa [Metric.mem_ball, not_lt, dist_eq_norm] at h1
    have hsuby : Sᶜ ⊆ {ζ : ℂ | 2 * δ ≤ ‖ζ - y‖} := by
      intro ζ hζ
      have h1 : ζ ∉ Metric.ball y (2 * δ) := fun h => hζ (by rw [hS]; exact Or.inr h)
      rwa [Metric.mem_ball, not_lt, dist_eq_norm] at h1
    have hfmeas : Measurable f := (Work.CR.Flat.Cauchy.continuous_of_holder hα hK0 hK).measurable
    have hWmeas : Measurable W := W_contDiff.continuous.measurable
    have hIntT1 : IntegrableOn T1 Sᶜ volume := by
      have hmaj : IntegrableOn (fun ζ : ℂ => 6 * K * δ * ‖ζ - x‖ ^ (α - 3)) Sᶜ volume :=
        ((integrableOn_exterior_rpow_shift x hspos (by linarith : α - 3 < -2)).mono_set hsubx
          ).const_mul _
      refine hmaj.mono' ?_ ?_
      · have hm : Measurable fun ζ : ℂ => (f ζ - f x) *
            (((ζ - x) ^ 2)⁻¹ - ((ζ - y) ^ 2)⁻¹) :=
          (hfmeas.sub measurable_const).mul
            ((((measurable_id.sub measurable_const).pow_const 2).inv).sub
              (((measurable_id.sub measurable_const).pow_const 2).inv))
        simpa only [hT1] using hm.aestronglyMeasurable.restrict
      · filter_upwards [ae_restrict_mem hSmeas.compl] with ζ hζ
        have hw : 0 < ‖ζ - x‖ := lt_of_lt_of_le hspos (hsubx hζ)
        have h1 : ‖f ζ - f x‖ ≤ K * ‖ζ - x‖ ^ α := hK ζ x
        have h2 : ‖((ζ - x) ^ 2)⁻¹ - ((ζ - y) ^ 2)⁻¹‖ ≤ 6 * δ / ‖ζ - x‖ ^ 3 := by
          have h3 : 2 * ‖(ζ - x) - (ζ - y)‖ ≤ ‖ζ - x‖ := by
            have hxy' : (ζ - x) - (ζ - y) = y - x := by ring
            rw [hxy', show ‖y - x‖ = δ from by rw [norm_sub_rev, hδdef]]
            exact hsubx hζ
          have h4 := norm_inv_sq_sub_inv_sq_le (u := ζ - x) (v := ζ - y) h3
          rwa [show (ζ - x) - (ζ - y) = y - x from by ring,
            show ‖y - x‖ = δ from by rw [norm_sub_rev, hδdef]] at h4
        have h3 : (‖ζ - x‖ ^ 3 : ℝ)⁻¹ = ‖ζ - x‖ ^ (-3 : ℝ) := by
          rw [← Real.rpow_natCast ‖ζ - x‖ 3, ← Real.rpow_neg hw.le]
          norm_num
        have h4 : ‖ζ - x‖ ^ (α - 3) = ‖ζ - x‖ ^ α * ‖ζ - x‖ ^ (-3 : ℝ) := by
          have hexp : (α : ℝ) - 3 = α + (-3 : ℝ) := by ring
          rw [hexp, Real.rpow_add hw]
        rw [hT1, norm_mul]
        calc ‖f ζ - f x‖ * ‖((ζ - x) ^ 2)⁻¹ - ((ζ - y) ^ 2)⁻¹‖
            ≤ (K * ‖ζ - x‖ ^ α) * (6 * δ / ‖ζ - x‖ ^ 3) :=
              mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
          _ = 6 * K * δ * ‖ζ - x‖ ^ (α - 3) := by
              rw [div_eq_mul_inv, h3, h4]
              ring
    have hIntT2 : IntegrableOn T2 Sᶜ volume := by
      have hmaj : IntegrableOn (fun ζ : ℂ => M * ‖W (ζ - x) - W (ζ - y)‖) Sᶜ volume :=
        (((hC₃ x y).1.norm).const_mul M).integrableOn
      refine hmaj.mono' ?_ ?_
      · have hm : Measurable fun ζ : ℂ => f x * (W (ζ - x) - W (ζ - y)) :=
          measurable_const.mul ((hWmeas.comp (measurable_id.sub measurable_const)).sub
            (hWmeas.comp (measurable_id.sub measurable_const)))
        simpa only [hT2] using hm.aestronglyMeasurable.restrict
      · filter_upwards [ae_restrict_mem hSmeas.compl] with ζ _
        show ‖f x * (W (ζ - x) - W (ζ - y))‖ ≤ M * ‖W (ζ - x) - W (ζ - y)‖
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _)
    have hbumpmeas : Measurable fun ζ : ℂ => (bumpC (ζ - y) : ℂ) :=
      (Complex.continuous_ofReal.comp bumpC_contDiff.continuous).measurable.comp
        (measurable_id.sub measurable_const)
    have hInvmeas : Measurable fun ζ : ℂ => (((ζ - y) ^ 2)⁻¹) :=
      ((measurable_id.sub measurable_const).pow_const 2).inv
    have hIntT3 : IntegrableOn (fun ζ : ℂ => (bumpC (ζ - y) : ℂ) * (((ζ - y) ^ 2)⁻¹))
        Sᶜ volume := by
      have hbase : Integrable ((Metric.ball y 1).indicator (fun _ : ℂ => (1 : ℝ))) volume :=
        (integrableOn_const (s := Metric.ball y 1) (C := (1 : ℝ)) (by simp) (by norm_num)
          ).integrable_indicator measurableSet_ball
      have hmaj : IntegrableOn (fun ζ : ℂ => ((2 * δ) ^ 2)⁻¹ *
          (Metric.ball y 1).indicator (fun _ : ℂ => (1 : ℝ)) ζ) Sᶜ volume :=
        (hbase.const_mul ((2 * δ) ^ 2)⁻¹).integrableOn
      refine hmaj.mono' ?_ ?_
      · exact (hbumpmeas.mul hInvmeas).aestronglyMeasurable.restrict
      · filter_upwards [ae_restrict_mem hSmeas.compl] with ζ hζ
        have h1 : 2 * δ ≤ ‖ζ - y‖ := hsuby hζ
        by_cases h2 : ‖ζ - y‖ < 1
        · rw [Set.indicator_of_mem (by rw [Metric.mem_ball, dist_eq_norm]; exact h2), mul_one]
          have h3 : ‖(bumpC (ζ - y) : ℂ)‖ ≤ 1 := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (bumpC_nonneg _)]
            exact bumpC_le_one _
          have h4 : ‖(((ζ - y) ^ 2)⁻¹)‖ ≤ ((2 * δ) ^ 2)⁻¹ := by
            rw [norm_inv, norm_pow]
            have h5 : (2 * δ) ^ 2 ≤ ‖ζ - y‖ ^ 2 := by nlinarith
            exact inv_anti₀ (by positivity) h5
          rw [norm_mul]
          calc ‖(bumpC (ζ - y) : ℂ)‖ * ‖(((ζ - y) ^ 2)⁻¹)‖ ≤ 1 * ((2 * δ) ^ 2)⁻¹ :=
                mul_le_mul h3 h4 (norm_nonneg _) (by norm_num)
            _ = ((2 * δ) ^ 2)⁻¹ := one_mul _
        · have h3 : bumpC (ζ - y) = 0 := bumpC_eq_zero (le_of_not_gt h2)
          rw [Set.indicator_of_notMem (by rw [Metric.mem_ball, dist_eq_norm]; exact h2),
            mul_zero, h3, Complex.ofReal_zero, zero_mul, norm_zero]
    have hfar : ‖∫ ζ in Sᶜ, (Ix ζ - Iy ζ) ∂volume‖ ≤ (12 * Real.pi * 2 ^ (α - 1) / (1 - α) + C₃ + 12 + Real.pi) * (M + K) * δ ^ α := by
      rw [hcongr]
      have hsplit2 : ∫ ζ in Sᶜ, (T1 ζ + T2 ζ + T3 ζ) ∂volume
          = (∫ ζ in Sᶜ, T1 ζ ∂volume) + (∫ ζ in Sᶜ, T2 ζ ∂volume)
            + (∫ ζ in Sᶜ, T3 ζ ∂volume) := by
        have h1 : ∫ ζ in Sᶜ, (T1 ζ + T2 ζ + T3 ζ) ∂volume
            = ∫ ζ in Sᶜ, (((T1 + T2) + T3) ζ) ∂volume := by
          refine setIntegral_congr_fun hSmeas.compl (fun ζ _ => ?_)
          simp only [Pi.add_apply]
        have hInt12 : Integrable (T1 + T2) (volume.restrict Sᶜ) := by
          rw [show (T1 + T2) = fun ζ : ℂ => T1 ζ + T2 ζ from rfl]
          exact hIntT1.add hIntT2
        have hIntT3' : Integrable T3 (volume.restrict Sᶜ) := by
          rw [hT3]
          exact hIntT3.const_mul (f y - f x)
        have h2 : ∫ ζ in Sᶜ, (((T1 + T2) + T3) ζ) ∂volume
            = (∫ ζ in Sᶜ, ((T1 + T2) ζ) ∂volume) + (∫ ζ in Sᶜ, T3 ζ ∂volume) :=
          integral_add hInt12 hIntT3'
        have hIntT1' : Integrable T1 (volume.restrict Sᶜ) := by
          rw [hT1]; exact hIntT1
        have hIntT2' : Integrable T2 (volume.restrict Sᶜ) := by
          rw [hT2]; exact hIntT2
        have h3 : ∫ ζ in Sᶜ, ((T1 + T2) ζ) ∂volume
            = (∫ ζ in Sᶜ, T1 ζ ∂volume) + (∫ ζ in Sᶜ, T2 ζ ∂volume) :=
          integral_add hIntT1' hIntT2' 
        rw [h1, h2, h3]
      rw [hsplit2]
      have hT1b : ‖∫ ζ in Sᶜ, T1 ζ ∂volume‖
          ≤ 12 * Real.pi * 2 ^ (α - 1) / (1 - α) * (K * δ ^ α) := by
        have h := Holder.far_kernel_diff_bound hα1 hδpos hK (hδdef.symm)
        simpa only [hT1, hS] using h
      have hIntW2 : Integrable (fun ζ : ℂ => ‖W (ζ - x) - W (ζ - y)‖) volume :=
        (hC₃ x y).1.norm
      have hT2b : ‖∫ ζ in Sᶜ, T2 ζ ∂volume‖ ≤ M * (C₃ * δ) := by
        calc ‖∫ ζ in Sᶜ, T2 ζ ∂volume‖ ≤ ∫ ζ in Sᶜ, ‖T2 ζ‖ ∂volume :=
              norm_integral_le_integral_norm _
          _ ≤ ∫ ζ in Sᶜ, M * ‖W (ζ - x) - W (ζ - y)‖ ∂volume := by
              refine integral_mono (f := fun ζ => ‖T2 ζ‖)
                (g := fun ζ => M * ‖W (ζ - x) - W (ζ - y)‖) hIntT2.norm
                (hIntW2.const_mul M).integrableOn ?_
              intro ζ
              show ‖f x * (W (ζ - x) - W (ζ - y))‖ ≤ M * ‖W (ζ - x) - W (ζ - y)‖
              rw [norm_mul]
              exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _)
          _ = M * ∫ ζ in Sᶜ, ‖W (ζ - x) - W (ζ - y)‖ ∂volume := integral_const_mul M _
          _ ≤ M * ∫ ζ : ℂ, ‖W (ζ - x) - W (ζ - y)‖ ∂volume := by
              refine mul_le_mul_of_nonneg_left ?_ hM0
              rw [← integral_indicator hSmeas.compl]
              refine integral_mono (hIntW2.indicator hSmeas.compl) hIntW2 ?_
              intro ζ
              by_cases hζ : ζ ∈ Sᶜ
              · rw [Set.indicator_of_mem hζ]
              · rw [Set.indicator_of_notMem hζ]
                exact norm_nonneg _
          _ ≤ M * (C₃ * ‖x - y‖) := mul_le_mul_of_nonneg_left (hC₃ x y).2 hM0
          _ = M * (C₃ * δ) := by rw [hδdef]
      have hT3b : ‖∫ ζ in Sᶜ, T3 ζ ∂volume‖ ≤ (12 + Real.pi) * (K * δ ^ α) := by
        have h1 : ∫ ζ in Sᶜ, T3 ζ ∂volume
            = (f y - f x) * (∫ ζ in Sᶜ,
                (bumpC (ζ - y) : ℂ) * (((ζ - y) ^ 2)⁻¹) ∂volume) := by
          rw [hT3, ← integral_const_mul]
        have h2 : ‖∫ ζ in Sᶜ, (bumpC (ζ - y) : ℂ) * (((ζ - y) ^ 2)⁻¹) ∂volume‖
            ≤ 12 + Real.pi := by
          have h := Holder.far_chi_term_bound hδpos (hδdef.symm)
          simpa only [hS] using h
        have h3 : ‖f y - f x‖ ≤ K * δ ^ α := by
          have h := hK y x
          rw [show ‖y - x‖ = δ from by rw [norm_sub_rev, hδdef]] at h
          exact h
        rw [h1, norm_mul]
        calc ‖f y - f x‖ * ‖∫ ζ in Sᶜ,
              (bumpC (ζ - y) : ℂ) * (((ζ - y) ^ 2)⁻¹) ∂volume‖
            ≤ (K * δ ^ α) * (12 + Real.pi) :=
              mul_le_mul h3 h2 (norm_nonneg _) (by positivity)
          _ = (12 + Real.pi) * (K * δ ^ α) := by ring
      have hcomb : ‖(∫ ζ in Sᶜ, T1 ζ ∂volume) + (∫ ζ in Sᶜ, T2 ζ ∂volume)
            + (∫ ζ in Sᶜ, T3 ζ ∂volume)‖
          ≤ (12 * Real.pi * 2 ^ (α - 1) / (1 - α)) * (K * δ ^ α) + M * (C₃ * δ)
            + (12 + Real.pi) * (K * δ ^ α) := by
        have h4 : ‖(∫ ζ in Sᶜ, T1 ζ ∂volume) + (∫ ζ in Sᶜ, T2 ζ ∂volume)
              + (∫ ζ in Sᶜ, T3 ζ ∂volume)‖
            ≤ ‖(∫ ζ in Sᶜ, T1 ζ ∂volume) + (∫ ζ in Sᶜ, T2 ζ ∂volume)‖
              + ‖∫ ζ in Sᶜ, T3 ζ ∂volume‖ := norm_add_le _ _
        have h5 : ‖(∫ ζ in Sᶜ, T1 ζ ∂volume) + (∫ ζ in Sᶜ, T2 ζ ∂volume)‖
            ≤ ‖∫ ζ in Sᶜ, T1 ζ ∂volume‖ + ‖∫ ζ in Sᶜ, T2 ζ ∂volume‖ := norm_add_le _ _
        linarith [h4, h5, hT1b, hT2b, hT3b]
      have harith : (12 * Real.pi * 2 ^ (α - 1) / (1 - α)) * (K * δ ^ α) + M * (C₃ * δ)
            + (12 + Real.pi) * (K * δ ^ α) ≤ (12 * Real.pi * 2 ^ (α - 1) / (1 - α) + C₃ + 12 + Real.pi) * (M + K) * δ ^ α := by
        have hA0 : 0 ≤ 12 * Real.pi * 2 ^ (α - 1) / (1 - α) := by positivity
        have hC0 : 0 ≤ 12 + Real.pi := by positivity
        have hK' : K ≤ M + K := by linarith
        have hM' : M ≤ M + K := by linarith
        have hδa : δ ≤ δ ^ α := by
          have h2 : δ ^ (1 : ℝ) ≤ δ ^ α :=
            Real.rpow_le_rpow_of_exponent_ge hδpos hδle1 hα1.le
          rwa [Real.rpow_one] at h2
        have h1 : (12 * Real.pi * 2 ^ (α - 1) / (1 - α)) * (K * δ ^ α)
            ≤ (12 * Real.pi * 2 ^ (α - 1) / (1 - α)) * ((M + K) * δ ^ α) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hK' hδpowpos.le) hA0
        have h2 : (12 + Real.pi) * (K * δ ^ α) ≤ (12 + Real.pi) * ((M + K) * δ ^ α) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hK' hδpowpos.le) hC0
        have h3 : M * (C₃ * δ) ≤ C₃ * ((M + K) * δ ^ α) := by
          have h4 : M * δ ≤ (M + K) * δ ^ α := by
            calc M * δ ≤ (M + K) * δ := mul_le_mul_of_nonneg_right hM' hδpos.le
              _ ≤ (M + K) * δ ^ α := mul_le_mul_of_nonneg_left hδa (by positivity)
          calc M * (C₃ * δ) = C₃ * (M * δ) := by ring
            _ ≤ C₃ * ((M + K) * δ ^ α) := mul_le_mul_of_nonneg_left h4 hC₃pos.le
        have h5 : (12 * Real.pi * 2 ^ (α - 1) / (1 - α) + C₃ + 12 + Real.pi) * (M + K) * δ ^ α
            = (12 * Real.pi * 2 ^ (α - 1) / (1 - α)) * ((M + K) * δ ^ α)
              + C₃ * ((M + K) * δ ^ α) + (12 + Real.pi) * ((M + K) * δ ^ α) := by
          ring
        linarith [h1, h2, h3, h5]
      linarith [hcomb, harith]
    -- ===== conclusion of the main case =====
    rw [hbeur, hsplit]
    have hsum : ‖(∫ ζ in S, (Ix ζ - Iy ζ) ∂volume) + (∫ ζ in Sᶜ, (Ix ζ - Iy ζ) ∂volume)‖
        ≤ ((12 * Real.pi / α + 72 * Real.pi) + (12 * Real.pi * 2 ^ (α - 1) / (1 - α) + C₃ + 12 + Real.pi)) * (M + K) * δ ^ α := by
      have h4 : ‖(∫ ζ in S, (Ix ζ - Iy ζ) ∂volume) + (∫ ζ in Sᶜ, (Ix ζ - Iy ζ) ∂volume)‖
          ≤ ‖∫ ζ in S, (Ix ζ - Iy ζ) ∂volume‖ + ‖∫ ζ in Sᶜ, (Ix ζ - Iy ζ) ∂volume‖ :=
        norm_add_le _ _
      have h5 : ‖∫ ζ in S, (Ix ζ - Iy ζ) ∂volume‖ + ‖∫ ζ in Sᶜ, (Ix ζ - Iy ζ) ∂volume‖
          ≤ (12 * Real.pi / α + 72 * Real.pi) * (M + K) * δ ^ α + (12 * Real.pi * 2 ^ (α - 1) / (1 - α) + C₃ + 12 + Real.pi) * (M + K) * δ ^ α := add_le_add hnear hfar
      have h6 : (12 * Real.pi / α + 72 * Real.pi) * (M + K) * δ ^ α + (12 * Real.pi * 2 ^ (α - 1) / (1 - α) + C₃ + 12 + Real.pi) * (M + K) * δ ^ α
          = ((12 * Real.pi / α + 72 * Real.pi) + (12 * Real.pi * 2 ^ (α - 1) / (1 - α) + C₃ + 12 + Real.pi)) * (M + K) * δ ^ α := by ring
      linarith [h4, h5, h6]
    have hfin : Real.pi⁻¹ * (((12 * Real.pi / α + 72 * Real.pi) + (12 * Real.pi * 2 ^ (α - 1) / (1 - α) + C₃ + 12 + Real.pi)) * (M + K) * δ ^ α)
        ≤ (max ((12 * Real.pi / α + 72 * Real.pi) + (12 * Real.pi * 2 ^ (α - 1) / (1 - α) + C₃ + 12 + Real.pi)) (2 * (2 / α + 10)) + 1) * (M + K) * (1 + R) * δ ^ α := by
      have hpi : Real.pi⁻¹ ≤ 1 := by
        rw [inv_le_one₀ Real.pi_pos]
        linarith [Real.pi_gt_three]
      have h1 : 0 ≤ ((12 * Real.pi / α + 72 * Real.pi) + (12 * Real.pi * 2 ^ (α - 1) / (1 - α) + C₃ + 12 + Real.pi)) * (M + K) * δ ^ α := by positivity
      have h2 : 0 ≤ (M + K) * δ ^ α := by positivity
      have h3 : (12 * Real.pi / α + 72 * Real.pi) + (12 * Real.pi * 2 ^ (α - 1) / (1 - α) + C₃ + 12 + Real.pi) ≤ max ((12 * Real.pi / α + 72 * Real.pi) + (12 * Real.pi * 2 ^ (α - 1) / (1 - α) + C₃ + 12 + Real.pi)) (2 * (2 / α + 10)) + 1 := by
        have := le_max_left ((12 * Real.pi / α + 72 * Real.pi) + (12 * Real.pi * 2 ^ (α - 1) / (1 - α) + C₃ + 12 + Real.pi)) (2 * (2 / α + 10)); linarith
      have h4 : (1 : ℝ) ≤ 1 + R := by linarith
      have h8 : 0 ≤ (max ((12 * Real.pi / α + 72 * Real.pi) + (12 * Real.pi * 2 ^ (α - 1) / (1 - α) + C₃ + 12 + Real.pi)) (2 * (2 / α + 10)) + 1) * (M + K) * δ ^ α := by positivity
      calc Real.pi⁻¹ * (((12 * Real.pi / α + 72 * Real.pi) + (12 * Real.pi * 2 ^ (α - 1) / (1 - α) + C₃ + 12 + Real.pi)) * (M + K) * δ ^ α)
          ≤ 1 * (((12 * Real.pi / α + 72 * Real.pi) + (12 * Real.pi * 2 ^ (α - 1) / (1 - α) + C₃ + 12 + Real.pi)) * (M + K) * δ ^ α) := mul_le_mul_of_nonneg_right hpi h1
        _ = ((12 * Real.pi / α + 72 * Real.pi) + (12 * Real.pi * 2 ^ (α - 1) / (1 - α) + C₃ + 12 + Real.pi)) * (M + K) * δ ^ α := one_mul _
        _ ≤ (max ((12 * Real.pi / α + 72 * Real.pi) + (12 * Real.pi * 2 ^ (α - 1) / (1 - α) + C₃ + 12 + Real.pi)) (2 * (2 / α + 10)) + 1) * (M + K) * δ ^ α := by
            have h5 : ((12 * Real.pi / α + 72 * Real.pi) + (12 * Real.pi * 2 ^ (α - 1) / (1 - α) + C₃ + 12 + Real.pi)) * ((M + K) * δ ^ α)
                ≤ (max ((12 * Real.pi / α + 72 * Real.pi) + (12 * Real.pi * 2 ^ (α - 1) / (1 - α) + C₃ + 12 + Real.pi)) (2 * (2 / α + 10)) + 1) * ((M + K) * δ ^ α) :=
              mul_le_mul_of_nonneg_right h3 h2
            linarith [h5]
        _ ≤ (max ((12 * Real.pi / α + 72 * Real.pi) + (12 * Real.pi * 2 ^ (α - 1) / (1 - α) + C₃ + 12 + Real.pi)) (2 * (2 / α + 10)) + 1) * (M + K) * (1 + R) * δ ^ α := by
            calc (max ((12 * Real.pi / α + 72 * Real.pi) + (12 * Real.pi * 2 ^ (α - 1) / (1 - α) + C₃ + 12 + Real.pi)) (2 * (2 / α + 10)) + 1) * (M + K) * δ ^ α
                = (max ((12 * Real.pi / α + 72 * Real.pi) + (12 * Real.pi * 2 ^ (α - 1) / (1 - α) + C₃ + 12 + Real.pi)) (2 * (2 / α + 10)) + 1) * (M + K) * δ ^ α * 1 := by ring
              _ ≤ (max ((12 * Real.pi / α + 72 * Real.pi) + (12 * Real.pi * 2 ^ (α - 1) / (1 - α) + C₃ + 12 + Real.pi)) (2 * (2 / α + 10)) + 1) * (M + K) * δ ^ α * (1 + R) :=
                  mul_le_mul_of_nonneg_left h4 h8
              _ = (max ((12 * Real.pi / α + 72 * Real.pi) + (12 * Real.pi * 2 ^ (α - 1) / (1 - α) + C₃ + 12 + Real.pi)) (2 * (2 / α + 10)) + 1) * (M + K) * (1 + R) * δ ^ α := by ring
    calc Real.pi⁻¹ * ‖(∫ ζ in S, (Ix ζ - Iy ζ) ∂volume) + (∫ ζ in Sᶜ, (Ix ζ - Iy ζ) ∂volume)‖
        ≤ Real.pi⁻¹ * (((12 * Real.pi / α + 72 * Real.pi) + (12 * Real.pi * 2 ^ (α - 1) / (1 - α) + C₃ + 12 + Real.pi)) * (M + K) * δ ^ α) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ (max ((12 * Real.pi / α + 72 * Real.pi) + (12 * Real.pi * 2 ^ (α - 1) / (1 - α) + C₃ + 12 + Real.pi)) (2 * (2 / α + 10)) + 1) * (M + K) * (1 + R) * δ ^ α := hfin
  · -- ================= case `δ > 1` =================
    have hδgt : 1 < ‖x - y‖ := lt_of_not_ge hδle
    have hδ1 : 1 ≤ ‖x - y‖ := le_of_lt hδgt
    have hδpow : 1 ≤ ‖x - y‖ ^ α := Real.one_le_rpow hδ1 hα.le
    have hcast : 2 * (2 / α + 10) ≤ max ((12 * Real.pi / α + 72 * Real.pi) + (12 * Real.pi * 2 ^ (α - 1) / (1 - α) + C₃ + 12 + Real.pi)) (2 * (2 / α + 10)) + 1 := by
      have := le_max_right ((12 * Real.pi / α + 72 * Real.pi) + (12 * Real.pi * 2 ^ (α - 1) / (1 - α) + C₃ + 12 + Real.pi)) (2 * (2 / α + 10)); linarith
    have h1 : 2 * (2 / α + 10) * (M + K) * (1 + R)
        ≤ (max ((12 * Real.pi / α + 72 * Real.pi) + (12 * Real.pi * 2 ^ (α - 1) / (1 - α) + C₃ + 12 + Real.pi)) (2 * (2 / α + 10)) + 1) * (M + K) * (1 + R) := by
      have h3 : 0 ≤ (M + K) * (1 + R) := by positivity
      nlinarith [hcast, h3]
    have h2 : (max ((12 * Real.pi / α + 72 * Real.pi) + (12 * Real.pi * 2 ^ (α - 1) / (1 - α) + C₃ + 12 + Real.pi)) (2 * (2 / α + 10)) + 1) * (M + K) * (1 + R)
        ≤ (max ((12 * Real.pi / α + 72 * Real.pi) + (12 * Real.pi * 2 ^ (α - 1) / (1 - α) + C₃ + 12 + Real.pi)) (2 * (2 / α + 10)) + 1) * (M + K) * (1 + R) * ‖x - y‖ ^ α := by
      have h4 : 0 ≤ (max ((12 * Real.pi / α + 72 * Real.pi) + (12 * Real.pi * 2 ^ (α - 1) / (1 - α) + C₃ + 12 + Real.pi)) (2 * (2 / α + 10)) + 1) * (M + K) * (1 + R) := by positivity
      nlinarith [h4, hδpow]
    calc ‖beurling f x - beurling f y‖
        ≤ ‖beurling f x‖ + ‖beurling f y‖ := norm_sub_le _ _
      _ ≤ (2 / α + 10) * (M + K) * (1 + R) + (2 / α + 10) * (M + K) * (1 + R) := add_le_add (hC₂ x) (hC₂ y)
      _ = 2 * (2 / α + 10) * (M + K) * (1 + R) := by ring
      _ ≤ (max ((12 * Real.pi / α + 72 * Real.pi) + (12 * Real.pi * 2 ^ (α - 1) / (1 - α) + C₃ + 12 + Real.pi)) (2 * (2 / α + 10)) + 1) * (M + K) * (1 + R) := h1
      _ ≤ (max ((12 * Real.pi / α + 72 * Real.pi) + (12 * Real.pi * 2 ^ (α - 1) / (1 - α) + C₃ + 12 + Real.pi)) (2 * (2 / α + 10)) + 1) * (M + K) * (1 + R) * ‖x - y‖ ^ α := h2

/-- **Schauder (Calderón–Zygmund) estimates for the Beurling transform, uniform in the function.**
If `f` is bounded by `M`, globally `α`-Hölder with constant `K` (`0 < α < 1`) and supported in the
ball of radius `R`, then `beurling f` is bounded by `C(α) (M+K) (1+R)` and globally `α`-Hölder with
constant `C(α) (M+K) (1+R)`, with `C(α)` depending only on `α` (and not on `f`, `M`, `K`, `R`). -/
theorem beurling_holder_uniform :
    ∃ Cfun : ℝ → ℝ, (∀ α, 0 < α → 0 < Cfun α) ∧
      ∀ (α M K R : ℝ) (f : ℂ → ℂ), 0 < α → α < 1 → 0 ≤ R →
        (∀ z, ‖f z‖ ≤ M) → (∀ x y : ℂ, ‖f x - f y‖ ≤ K * ‖x - y‖ ^ α) →
        (∀ z, R < ‖z‖ → f z = 0) →
        (∀ z, ‖beurling f z‖ ≤ Cfun α * (M + K) * (1 + R)) ∧
        (∀ x y : ℂ, ‖beurling f x - beurling f y‖ ≤
          Cfun α * (M + K) * (1 + R) * ‖x - y‖ ^ α) := by
  obtain ⟨C₃, hC₃pos, hC₃⟩ := Holder.W_translate_L1_bound
  refine ⟨fun α => max ((12 * Real.pi / α + 72 * Real.pi) + (12 * Real.pi * 2 ^ (α - 1) / (1 - α) + C₃ + 12 + Real.pi)) (2 * (2 / α + 10)) + 1, ?_, ?_⟩
  · intro α hα
    have h2 : (0 : ℝ) < 2 * (2 / α + 10) := by positivity
    have h3 : 2 * (2 / α + 10) ≤ max ((12 * Real.pi / α + 72 * Real.pi) + (12 * Real.pi * 2 ^ (α - 1) / (1 - α) + C₃ + 12 + Real.pi)) (2 * (2 / α + 10)) := le_max_right _ _
    linarith
  · intro α M K R f hα hα1 hR hM hK hsupp
    have hM0 : 0 ≤ M := le_trans (norm_nonneg (f 0)) (hM 0)
    have hK0 : 0 ≤ K := by
      have h := hK 0 1
      rw [show (0 : ℂ) - 1 = -(1 : ℂ) from by ring, norm_neg, norm_one, Real.one_rpow,
        mul_one] at h
      linarith [norm_nonneg (f 0 - f 1)]
    have hMK : 0 ≤ M + K := by linarith
    have h1R : 0 ≤ 1 + R := by linarith
    have hle : (2 / α + 10) ≤ max ((12 * Real.pi / α + 72 * Real.pi) + (12 * Real.pi * 2 ^ (α - 1) / (1 - α) + C₃ + 12 + Real.pi)) (2 * (2 / α + 10)) + 1 := by
      have h2 : (0 : ℝ) < 2 / α + 10 := by positivity
      have h3 : 2 * (2 / α + 10) ≤ max ((12 * Real.pi / α + 72 * Real.pi) + (12 * Real.pi * 2 ^ (α - 1) / (1 - α) + C₃ + 12 + Real.pi)) (2 * (2 / α + 10)) := le_max_right _ _
      linarith
    constructor
    · intro z
      have h := beurling_bounded_uniform hα hα1 hR f hM hK hsupp z
      calc ‖beurling f z‖ ≤ (2 / α + 10) * (M + K) * (1 + R) := h
        _ ≤ (max ((12 * Real.pi / α + 72 * Real.pi) + (12 * Real.pi * 2 ^ (α - 1) / (1 - α) + C₃ + 12 + Real.pi)) (2 * (2 / α + 10)) + 1) * (M + K) * (1 + R) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle hMK) h1R
    · intro x y
      exact beurling_holder_diff_bound hα hα1 hR f hM hK hsupp hC₃ hC₃pos x y

end Work.Beltrami
