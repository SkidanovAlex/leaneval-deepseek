import Mathlib
import Submission.Work.Asymptotics.K24FBase
import Submission.Work.Asymptotics.K24FZ
import Submission.Work.Asymptotics.K24FDefs
import Submission.Work.FunnelNumerics.E4_funnel_bounds
import Submission.Work.Asymptotics.Compact.zsmall

set_option maxHeartbeats 1000000

namespace Work.Asymptotics

open UpperHalfPlane
open Work.Kernels

noncomputable section

namespace K24Fsm

/-! ## Elementary helpers -/

lemma norm_sum3_le {a b c : ℂ} : ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
  have h1 := norm_add_le (a + b) c
  have h2 := norm_add_le a b
  linarith

lemma norm_sum4_le {a b c d : ℂ} : ‖a + b + c + d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
  have h1 := norm_add_le (a + b + c) d
  have h2 := norm_add_le (a + b) c
  have h3 := norm_add_le a b
  linarith

lemma norm_sum5_le {a b c d e : ℂ} : ‖a + b + c + d + e‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ := by
  have h1 := norm_add_le (a + b + c + d) e
  have h2 := norm_add_le (a + b + c) d
  have h3 := norm_add_le (a + b) c
  have h4 := norm_add_le a b
  linarith

lemma norm_sum7_le {a b c d e f g : ℂ} :
    ‖a + b + c + d + e + f + g‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ + ‖f‖ + ‖g‖ := by
  have h1 := norm_add_le (a + b + c + d + e + f) g
  have h2 := norm_add_le (a + b + c + d + e) f
  have h3 := norm_add_le (a + b + c + d) e
  have h4 := norm_add_le (a + b + c) d
  have h5 := norm_add_le (a + b) c
  have h6 := norm_add_le a b
  linarith


/-- `‖a * b‖ ≤ A * B` from `‖a‖ ≤ A`, `‖b‖ ≤ B`. -/
lemma norm_mul_le_mul {a b : ℂ} {A B : ℝ} (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B) : ‖a * b‖ ≤ A * B := by
  rw [norm_mul]
  exact mul_le_mul ha hb (norm_nonneg _) (le_trans (norm_nonneg a) ha)

lemma S0_eq_S0c : K24F.S0 = Small.S0c := rfl

lemma qnorm_pos (z : ℍ) : 0 < ‖qParamFun z‖ := by
  rw [norm_qParamFun]; exact Real.exp_pos _

lemma qsq_mul_qinv (z : ℍ) : ‖qParamFun z‖ ^ 2 * ‖qParamFun z‖⁻¹ = ‖qParamFun z‖ := by
  rw [pow_two, mul_assoc, mul_inv_cancel₀ (ne_of_gt (qnorm_pos z)), mul_one]

/-! ## The `z`-deviations at the threshold `Im z ≥ 3` -/

theorem zdev : ∃ A : ℝ, 0 < A ∧ ∀ z : ℍ, 3 ≤ z.im →
      ‖E4Fun z - 1‖ ≤ A * ‖qParamFun z‖ ∧
      ‖E4Fun z ^ 3 - 1‖ ≤ A * ‖qParamFun z‖ ∧
      ‖E2S z ^ 2 - Small.S0c z ^ 2‖ ≤ A * ‖qParamFun z‖ ∧
      ‖E6Fun z * E2S z / E4Fun z - Small.S0c z‖ ≤ A * ‖qParamFun z‖ ∧
      ‖E6Fun z * E2S z / E4Fun z - Small.S0c z + 24 * qParamFun z
          + 744 * qParamFun z * Small.S0c z‖ ≤ A * ‖qParamFun z‖ ^ 2 ∧
      ‖E2S z - Small.S0c z + 24 * qParamFun z‖ ≤ A * ‖qParamFun z‖ ^ 2 ∧
      ‖E4Fun z - 1 - 240 * qParamFun z‖ ≤ A * ‖qParamFun z‖ ^ 2 ∧
      ‖qParamFun z / DeltaFun z - 1‖ ≤ A * ‖qParamFun z‖ ∧
      ‖(DeltaFun z)⁻¹ - (qParamFun z)⁻¹ - 24‖ ≤ A * ‖qParamFun z‖ ∧
      ‖1 - DeltaFun z / qParamFun z‖ ≤ A * ‖qParamFun z‖ ∧
      (1 / 2) * ‖qParamFun z‖ ≤ ‖DeltaFun z‖ ∧
      ‖(DeltaFun z)⁻¹‖ ≤ A * ‖qParamFun z‖⁻¹ ∧
      ‖(E4Fun z)⁻¹‖ ≤ 2 ∧
      ‖E4Fun z‖ ≤ 3 / 2 ∧
      ‖Small.S0c z‖ ≤ 3 := by
  obtain ⟨a1, ha1p, ha1⟩ := Small.E4_sub_one
  obtain ⟨a2, ha2p, ha2⟩ := Small.E4_cube_sub_one
  obtain ⟨a3, ha3p, ha3⟩ := Small.E2S_sq_sub_S0c_sq
  obtain ⟨a4, ha4p, ha4⟩ := K24F.E6_E2S_div_E4_sub_S0c_three
  obtain ⟨a5, ha5p, ha5⟩ := K24F.E6_E2S_div_E4_second_three
  obtain ⟨a6, ha6p, ha6⟩ := Small.E2_sub_one_second
  obtain ⟨a7, ha7p, ha7⟩ := Small.E4_sub_one_second
  obtain ⟨a8, ha8p, ha8⟩ := q_div_Delta_sub_one_small
  obtain ⟨a9, ha9p, ha9⟩ := Small.delta_inv_small
  obtain ⟨a10, ha10p, ha10⟩ := Small.one_sub_delta_div_q
  obtain ⟨a11, ha11p, ha11⟩ := Small.delta_inv_bound
  set A : ℝ := 1 + a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + a10 + a11 with hA
  have hApos : 0 < A := by rw [hA]; positivity
  have h1A : a1 ≤ A := by rw [hA]; linarith
  have h2A : a2 ≤ A := by rw [hA]; linarith
  have h3A : a3 ≤ A := by rw [hA]; linarith
  have h4A : a4 ≤ A := by rw [hA]; linarith
  have h5A : a5 ≤ A := by rw [hA]; linarith
  have h6A : a6 ≤ A := by rw [hA]; linarith
  have h7A : a7 ≤ A := by rw [hA]; linarith
  have h8A : a8 ≤ A := by rw [hA]; linarith
  have h9A : a9 ≤ A := by rw [hA]; linarith
  have h10A : a10 ≤ A := by rw [hA]; linarith
  have h11A : a11 ≤ A := by rw [hA]; linarith
  refine ⟨A, hApos, fun z hz => ?_⟩
  have hz1 : (1:ℝ) ≤ z.im := by linarith
  have hq0 : (0:ℝ) ≤ ‖qParamFun z‖ := norm_nonneg _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc ‖E4Fun z - 1‖ ≤ a1 * ‖qParamFun z‖ := by simpa using ha1 z hz1
      _ ≤ A * ‖qParamFun z‖ := mul_le_mul_of_nonneg_right h1A hq0
  · calc ‖E4Fun z ^ 3 - 1‖ ≤ a2 * ‖qParamFun z‖ := by simpa using ha2 z hz1
      _ ≤ A * ‖qParamFun z‖ := mul_le_mul_of_nonneg_right h2A hq0
  · calc ‖E2S z ^ 2 - Small.S0c z ^ 2‖ ≤ a3 * ‖qParamFun z‖ := by simpa using ha3 z hz1
      _ ≤ A * ‖qParamFun z‖ := mul_le_mul_of_nonneg_right h3A hq0
  · calc ‖E6Fun z * E2S z / E4Fun z - Small.S0c z‖ ≤ a4 * ‖qParamFun z‖ := by
          simpa using ha4 z hz
      _ ≤ A * ‖qParamFun z‖ := mul_le_mul_of_nonneg_right h4A hq0
  · calc ‖E6Fun z * E2S z / E4Fun z - Small.S0c z + 24 * qParamFun z
          + 744 * qParamFun z * Small.S0c z‖ ≤ a5 * ‖qParamFun z‖ ^ 2 := ha5 z hz
      _ ≤ A * ‖qParamFun z‖ ^ 2 := mul_le_mul_of_nonneg_right h5A (by positivity)
  · have heq : E2S z - Small.S0c z + 24 * qParamFun z
        = E2Fun z - 1 + 24 * qParamFun z := by
      rw [TildeFacts.E2S_eq, Small.S0c]; ring
    rw [heq]
    calc ‖E2Fun z - 1 + 24 * qParamFun z‖ ≤ a6 * ‖qParamFun z‖ ^ 2 := ha6 z hz1
      _ ≤ A * ‖qParamFun z‖ ^ 2 := mul_le_mul_of_nonneg_right h6A (by positivity)
  · calc ‖E4Fun z - 1 - 240 * qParamFun z‖ ≤ a7 * ‖qParamFun z‖ ^ 2 := ha7 z hz1
      _ ≤ A * ‖qParamFun z‖ ^ 2 := mul_le_mul_of_nonneg_right h7A (by positivity)
  · calc ‖qParamFun z / DeltaFun z - 1‖ ≤ a8 * ‖qParamFun z‖ := by simpa using ha8 z hz1
      _ ≤ A * ‖qParamFun z‖ := mul_le_mul_of_nonneg_right h8A hq0
  · calc ‖(DeltaFun z)⁻¹ - (qParamFun z)⁻¹ - 24‖ ≤ a9 * ‖qParamFun z‖ := by
          simpa using ha9 z hz1
      _ ≤ A * ‖qParamFun z‖ := mul_le_mul_of_nonneg_right h9A hq0
  · calc ‖1 - DeltaFun z / qParamFun z‖ ≤ a10 * ‖qParamFun z‖ := by simpa using ha10 z hz1
      _ ≤ A * ‖qParamFun z‖ := mul_le_mul_of_nonneg_right h10A hq0
  · rw [norm_qParamFun]
    exact DeltaFun_funnel_lower_sharp (τ := z) (by linarith : 2 ≤ z.im)
  · calc ‖(DeltaFun z)⁻¹‖ ≤ a11 * ‖qParamFun z‖⁻¹ := ha11 z hz1
      _ ≤ A * ‖qParamFun z‖⁻¹ := mul_le_mul_of_nonneg_right h11A (by positivity)
  · exact K24F.E4_inv_le_two_three z hz
  · have h := Work.FunnelNumerics.E4_sub_one_le z (by linarith : 2 ≤ z.im)
    have h2 := norm_add_le (E4Fun z - 1) (1 : ℂ)
    rw [norm_one] at h2
    have h3 : ‖E4Fun z‖ ≤ ‖E4Fun z - 1‖ + 1 := by simpa using h2
    linarith
  · exact Small.S0c_norm_le z hz1

/-! ## The `τ`-coefficients -/

lemma phiref_jfree (τ z : ℍ) :
    K24F.Phiref τ z = 6 * (K24F.r0 τ + K24F.r2 τ) * (1 - K24F.S0 z ^ 2)
      + (12 * K24F.R0 τ - 12096 * K24F.r1 τ) * K24F.S0 z ^ 2
      + (-12 * K24F.R0 τ + 8640 * K24F.r1 τ) + 3456 * K24F.r1 τ * K24F.S0 z := by
  simp only [K24F.Phiref, K24F.Pref]
  rw [show K24F.r1 τ * (-12 * jInvariantFun τ + 8640 + (12 * jInvariantFun τ - 12096) * K24F.S0 z ^ 2)
      = (12 * (K24F.r1 τ * jInvariantFun τ) - 12096 * K24F.r1 τ) * K24F.S0 z ^ 2
        + (-12 * (K24F.r1 τ * jInvariantFun τ) + 8640 * K24F.r1 τ) from by ring,
    K24F.r1_mul_j τ]
  ring

lemma q1_jfree (τ z : ℍ) : K24F.Q1 τ z =
    (1440 + 288 * K24F.S0 z) * (K24F.r0 τ + K24F.r2 τ)
      + (-2880 * K24F.R0 τ + 2073600 * K24F.r1 τ - 576 * K24F.R0 τ * K24F.S0 z
          + 580608 * K24F.r1 τ * K24F.S0 z)
      - 82944 * K24F.r1 τ - 2571264 * K24F.r1 τ * K24F.S0 z := by
  simp only [K24F.Q1, K24F.P1]
  rw [show K24F.r1 τ * (-2880 * jInvariantFun τ + 2073600 - 576 * jInvariantFun τ * K24F.S0 z
        + 580608 * K24F.S0 z)
      = (-2880 * (K24F.r1 τ * jInvariantFun τ) + 2073600 * K24F.r1 τ
          - 576 * (K24F.r1 τ * jInvariantFun τ) * K24F.S0 z
          + 580608 * K24F.r1 τ * K24F.S0 z) from by ring,
    K24F.r1_mul_j τ]

theorem phiref_le : ∃ C : ℝ, 0 < C ∧ ∀ (τ z : ℍ), Funnel τ → 3 ≤ z.im →
    ‖K24F.Phiref τ z‖ ≤ C * scale τ := by
  obtain ⟨D, hD24, hDbd⟩ := K24F.tau_atom_bounds_D
  have hD0 : (0:ℝ) < D := by linarith
  refine ⟨128112 * D + 1, by positivity, fun τ z hτ hz => ?_⟩
  obtain ⟨hr0, hr2, hR0, hr1, hj, hΔ, hΔinv⟩ := hDbd τ hτ
  have hs0 : (0:ℝ) ≤ scale τ := (scale_pos τ).le
  have hS0 : ‖K24F.S0 z‖ ≤ 3 := K24F.zS0_norm z (by linarith)
  have hS0sq : ‖K24F.S0 z ^ 2‖ ≤ 9 := by
    rw [norm_pow]; nlinarith [hS0, norm_nonneg (K24F.S0 z)]
  have h1S0sq : ‖1 - K24F.S0 z ^ 2‖ ≤ 10 := by
    have h := norm_sub_le (1:ℂ) (K24F.S0 z ^ 2)
    rw [norm_one] at h; linarith
  have hr02 : ‖K24F.r0 τ + K24F.r2 τ‖ ≤ 2 * (D * scale τ) := by
    have h := norm_add_le (K24F.r0 τ) (K24F.r2 τ); linarith
  have hA : ‖6 * (K24F.r0 τ + K24F.r2 τ) * (1 - K24F.S0 z ^ 2)‖ ≤ 120 * D * scale τ := by
    calc ‖6 * (K24F.r0 τ + K24F.r2 τ) * (1 - K24F.S0 z ^ 2)‖
        = 6 * ‖K24F.r0 τ + K24F.r2 τ‖ * ‖1 - K24F.S0 z ^ 2‖ := by
          rw [norm_mul, norm_mul, Complex.norm_ofNat]
      _ ≤ 6 * (2 * (D * scale τ)) * 10 := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hr02 (by norm_num)) h1S0sq
            (norm_nonneg _) (by positivity)
      _ = 120 * D * scale τ := by ring
  have hB : ‖(12 * K24F.R0 τ - 12096 * K24F.r1 τ) * K24F.S0 z ^ 2‖ ≤ 108972 * D * scale τ := by
    rw [norm_mul]
    have hR : ‖12 * K24F.R0 τ - 12096 * K24F.r1 τ‖ ≤ 12108 * D * scale τ := by
      have h := norm_sub_le (12 * K24F.R0 τ) (12096 * K24F.r1 τ)
      rw [norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_ofNat] at h
      nlinarith [h, hR0, hr1]
    calc ‖12 * K24F.R0 τ - 12096 * K24F.r1 τ‖ * ‖K24F.S0 z ^ 2‖
        ≤ (12108 * D * scale τ) * 9 := mul_le_mul hR hS0sq (norm_nonneg _) (by positivity)
      _ = 108972 * D * scale τ := by ring
  have hC : ‖-12 * K24F.R0 τ + 8640 * K24F.r1 τ‖ ≤ 8652 * D * scale τ := by
    have h := norm_add_le (-((12 : ℂ) * K24F.R0 τ)) (8640 * K24F.r1 τ)
    rw [norm_neg, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_ofNat] at h
    have heq : -12 * K24F.R0 τ + 8640 * K24F.r1 τ
        = -((12 : ℂ) * K24F.R0 τ) + 8640 * K24F.r1 τ := by ring
    rw [heq]
    nlinarith [h, hR0, hr1]
  have hDl : ‖3456 * K24F.r1 τ * K24F.S0 z‖ ≤ 10368 * D * scale τ := by
    rw [norm_mul, norm_mul, Complex.norm_ofNat]
    calc 3456 * ‖K24F.r1 τ‖ * ‖K24F.S0 z‖ ≤ 3456 * (D * scale τ) * 3 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hr1 (by norm_num)) hS0 (norm_nonneg _) (by positivity)
      _ = 10368 * D * scale τ := by ring
  rw [phiref_jfree]
  calc ‖6 * (K24F.r0 τ + K24F.r2 τ) * (1 - K24F.S0 z ^ 2)
        + (12 * K24F.R0 τ - 12096 * K24F.r1 τ) * K24F.S0 z ^ 2
        + (-12 * K24F.R0 τ + 8640 * K24F.r1 τ) + 3456 * K24F.r1 τ * K24F.S0 z‖
      ≤ ‖6 * (K24F.r0 τ + K24F.r2 τ) * (1 - K24F.S0 z ^ 2)‖
        + ‖(12 * K24F.R0 τ - 12096 * K24F.r1 τ) * K24F.S0 z ^ 2‖
        + ‖-12 * K24F.R0 τ + 8640 * K24F.r1 τ‖ + ‖3456 * K24F.r1 τ * K24F.S0 z‖ := norm_sum4_le
    _ ≤ 120 * D * scale τ + 108972 * D * scale τ + 8652 * D * scale τ + 10368 * D * scale τ := by
        linarith
    _ = 128112 * D * scale τ := by ring
    _ ≤ (128112 * D + 1) * scale τ := by nlinarith [hs0]

theorem q1_le : ∃ C : ℝ, 0 < C ∧ ∀ (τ z : ℍ), Funnel τ → 3 ≤ z.im →
    ‖K24F.Q1 τ z‖ ≤ C * scale τ := by
  obtain ⟨D, hD24, hDbd⟩ := K24F.tau_atom_bounds_D
  have hD0 : (0:ℝ) < D := by linarith
  refine ⟨11621376 * D + 1, by positivity, fun τ z hτ hz => ?_⟩
  obtain ⟨hr0, hr2, hR0, hr1, hj, hΔ, hΔinv⟩ := hDbd τ hτ
  have hs0 : (0:ℝ) ≤ scale τ := (scale_pos τ).le
  have hS0 : ‖K24F.S0 z‖ ≤ 3 := K24F.zS0_norm z (by linarith)
  have hr02 : ‖K24F.r0 τ + K24F.r2 τ‖ ≤ 2 * (D * scale τ) := by
    have h := norm_add_le (K24F.r0 τ) (K24F.r2 τ); linarith
  have h1 : ‖(1440 + 288 * K24F.S0 z) * (K24F.r0 τ + K24F.r2 τ)‖ ≤ 4608 * D * scale τ := by
    rw [norm_mul]
    have hA : ‖(1440 : ℂ) + 288 * K24F.S0 z‖ ≤ 2304 := by
      have h := norm_add_le (1440 : ℂ) (288 * K24F.S0 z)
      rw [norm_mul] at h
      have hc1 : ‖(1440 : ℂ)‖ = 1440 := by norm_num
      have hc2 : ‖(288 : ℂ)‖ = 288 := by norm_num
      rw [hc1, hc2] at h
      linarith
    calc ‖(1440 : ℂ) + 288 * K24F.S0 z‖ * ‖K24F.r0 τ + K24F.r2 τ‖
        ≤ 2304 * (2 * (D * scale τ)) := mul_le_mul hA hr02 (norm_nonneg _) (by norm_num)
      _ = 4608 * D * scale τ := by ring
  have h2 : ‖-2880 * K24F.R0 τ‖ ≤ 2880 * D * scale τ := by
    rw [(show (-2880 : ℂ) * K24F.R0 τ = -((2880 : ℂ) * K24F.R0 τ) by ring), norm_neg, norm_mul]
    have hc : ‖(2880 : ℂ)‖ = 2880 := by norm_num
    rw [hc]
    linarith
  have h3 : ‖2073600 * K24F.r1 τ‖ ≤ 2073600 * D * scale τ := by
    rw [norm_mul]
    have hc : ‖(2073600 : ℂ)‖ = 2073600 := by norm_num
    rw [hc]
    linarith
  have h4 : ‖-576 * K24F.R0 τ * K24F.S0 z‖ ≤ 1728 * D * scale τ := by
    rw [(show (-576 : ℂ) * K24F.R0 τ * K24F.S0 z = -(((576 : ℂ) * K24F.R0 τ) * K24F.S0 z)
        by ring), norm_neg, norm_mul, norm_mul]
    have hc : ‖(576 : ℂ)‖ = 576 := by norm_num
    rw [hc]
    calc 576 * ‖K24F.R0 τ‖ * ‖K24F.S0 z‖ ≤ 576 * (D * scale τ) * 3 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hR0 (by norm_num)) hS0 (norm_nonneg _) (by positivity)
      _ = 1728 * D * scale τ := by ring
  have h5 : ‖580608 * K24F.r1 τ * K24F.S0 z‖ ≤ 1741824 * D * scale τ := by
    rw [norm_mul, norm_mul]
    have hc : ‖(580608 : ℂ)‖ = 580608 := by norm_num
    rw [hc]
    calc 580608 * ‖K24F.r1 τ‖ * ‖K24F.S0 z‖ ≤ 580608 * (D * scale τ) * 3 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hr1 (by norm_num)) hS0 (norm_nonneg _) (by positivity)
      _ = 1741824 * D * scale τ := by ring
  have h6 : ‖-(82944 * K24F.r1 τ)‖ ≤ 82944 * D * scale τ := by
    rw [norm_neg, norm_mul]
    have hc : ‖(82944 : ℂ)‖ = 82944 := by norm_num
    rw [hc]
    linarith
  have h7 : ‖-(2571264 * K24F.r1 τ * K24F.S0 z)‖ ≤ 7713792 * D * scale τ := by
    rw [norm_neg, norm_mul, norm_mul]
    have hc : ‖(2571264 : ℂ)‖ = 2571264 := by norm_num
    rw [hc]
    calc 2571264 * ‖K24F.r1 τ‖ * ‖K24F.S0 z‖ ≤ 2571264 * (D * scale τ) * 3 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hr1 (by norm_num)) hS0 (norm_nonneg _) (by positivity)
      _ = 7713792 * D * scale τ := by ring
  rw [q1_jfree]
  have heq : (1440 + 288 * K24F.S0 z) * (K24F.r0 τ + K24F.r2 τ)
      + (-2880 * K24F.R0 τ + 2073600 * K24F.r1 τ - 576 * K24F.R0 τ * K24F.S0 z
          + 580608 * K24F.r1 τ * K24F.S0 z)
      - 82944 * K24F.r1 τ - 2571264 * K24F.r1 τ * K24F.S0 z
      = (1440 + 288 * K24F.S0 z) * (K24F.r0 τ + K24F.r2 τ)
        + (-2880 * K24F.R0 τ) + (2073600 * K24F.r1 τ) + (-576 * K24F.R0 τ * K24F.S0 z)
        + (580608 * K24F.r1 τ * K24F.S0 z) + (-(82944 * K24F.r1 τ))
        + (-(2571264 * K24F.r1 τ * K24F.S0 z)) := by ring
  rw [heq]
  calc ‖(1440 + 288 * K24F.S0 z) * (K24F.r0 τ + K24F.r2 τ) + (-2880 * K24F.R0 τ)
        + (2073600 * K24F.r1 τ) + (-576 * K24F.R0 τ * K24F.S0 z)
        + (580608 * K24F.r1 τ * K24F.S0 z) + (-(82944 * K24F.r1 τ))
        + (-(2571264 * K24F.r1 τ * K24F.S0 z))‖
      ≤ ‖(1440 + 288 * K24F.S0 z) * (K24F.r0 τ + K24F.r2 τ)‖ + ‖-2880 * K24F.R0 τ‖
        + ‖2073600 * K24F.r1 τ‖ + ‖-576 * K24F.R0 τ * K24F.S0 z‖
        + ‖580608 * K24F.r1 τ * K24F.S0 z‖ + ‖-(82944 * K24F.r1 τ)‖
        + ‖-(2571264 * K24F.r1 τ * K24F.S0 z)‖ := norm_sum7_le
    _ ≤ 4608 * D * scale τ + 2880 * D * scale τ + 2073600 * D * scale τ + 1728 * D * scale τ
        + 1741824 * D * scale τ + 82944 * D * scale τ + 7713792 * D * scale τ := by
        linarith
    _ = 11621376 * D * scale τ := by ring
    _ ≤ (11621376 * D + 1) * scale τ := by nlinarith [hs0]
theorem uref_le : ∃ C : ℝ, 0 < C ∧ ∀ (τ z : ℍ), Funnel τ → 1 ≤ z.im →
    ‖K24F.Uref τ z‖ ≤ C * scale τ := by
  obtain ⟨D, hD24, hDbd⟩ := K24F.tau_atom_bounds_D
  have hD0 : (0:ℝ) < D := by linarith
  refine ⟨17280 * D + 1, by positivity, fun τ z hτ hz => ?_⟩
  obtain ⟨hr0, hr2, hR0, hr1, hj, hΔ, hΔinv⟩ := hDbd τ hτ
  have hs0 : (0:ℝ) ≤ scale τ := (scale_pos τ).le
  have hS0 : ‖K24F.S0 z‖ ≤ 3 := K24F.zS0_norm z hz
  have hS0sq : ‖K24F.S0 z ^ 2‖ ≤ 9 := by
    rw [norm_pow]; nlinarith [hS0, norm_nonneg (K24F.S0 z)]
  rw [K24F.Uref]
  have h1 : ‖(1728 : ℂ) * K24F.r0 τ * K24F.S0 z ^ 2‖ ≤ 15552 * D * scale τ := by
    have hA : ‖(1728 : ℂ) * K24F.r0 τ‖ ≤ 1728 * (D * scale τ) := by
      rw [norm_mul, Complex.norm_ofNat]
      exact mul_le_mul_of_nonneg_left hr0 (by norm_num)
    calc ‖(1728 : ℂ) * K24F.r0 τ * K24F.S0 z ^ 2‖
        ≤ (1728 * (D * scale τ)) * 9 := norm_mul_le_mul hA hS0sq
      _ = 15552 * D * scale τ := by ring
  have h2 : ‖(1728 : ℂ) * K24F.r2 τ‖ ≤ 1728 * D * scale τ := by
    rw [norm_mul, Complex.norm_ofNat]
    nlinarith [hr2]
  calc ‖(1728 : ℂ) * K24F.r0 τ * K24F.S0 z ^ 2 + 1728 * K24F.r2 τ‖
      ≤ ‖(1728 : ℂ) * K24F.r0 τ * K24F.S0 z ^ 2‖ + ‖(1728 : ℂ) * K24F.r2 τ‖ := norm_add_le _ _
    _ ≤ 15552 * D * scale τ + 1728 * D * scale τ := by linarith
    _ = 17280 * D * scale τ := by ring
    _ ≤ (17280 * D + 1) * scale τ := by nlinarith [hs0]

theorem th0_le : ∃ C : ℝ, 0 < C ∧ ∀ (τ z : ℍ), Funnel τ → 3 ≤ z.im →
    ‖K24F.Th0 τ z‖ ≤ C * scale τ := by
  obtain ⟨CQ, hCQp, hCQ⟩ := q1_le
  obtain ⟨CP, hCPp, hCP⟩ := phiref_le
  obtain ⟨CU, hCUp, hCU⟩ := uref_le
  obtain ⟨D, hD24, hDbd⟩ := K24F.tau_atom_bounds_D
  have hD0 : (0:ℝ) < D := by linarith
  refine ⟨CQ + 24 * CP + CU + 10368 * D + 1, by positivity, fun τ z hτ hz => ?_⟩
  obtain ⟨hr0, hr2, hR0, hr1, hj, hΔ, hΔinv⟩ := hDbd τ hτ
  have hs0 : (0:ℝ) ≤ scale τ := (scale_pos τ).le
  have hS0 : ‖K24F.S0 z‖ ≤ 3 := K24F.zS0_norm z (by linarith)
  have hQ := hCQ τ z hτ hz
  have hP := hCP τ z hτ hz
  have hU := hCU τ z hτ (by linarith : 1 ≤ z.im)
  have hR : ‖3456 * K24F.R0 τ * K24F.S0 z‖ ≤ 10368 * D * scale τ := by
    have hA : ‖(3456 : ℂ) * K24F.R0 τ‖ ≤ 3456 * (D * scale τ) := by
      rw [norm_mul, Complex.norm_ofNat]
      exact mul_le_mul_of_nonneg_left hR0 (by norm_num)
    calc ‖(3456 : ℂ) * K24F.R0 τ * K24F.S0 z‖ ≤ (3456 * (D * scale τ)) * 3 :=
          norm_mul_le_mul hA hS0
      _ = 10368 * D * scale τ := by ring
  have h24 : ‖(24 : ℂ) * K24F.Phiref τ z‖ ≤ 24 * CP * scale τ := by
    rw [norm_mul, Complex.norm_ofNat]
    nlinarith [hP]
  have hmain : ‖K24F.Q1 τ z + 24 * K24F.Phiref τ z - K24F.Uref τ z
        + 3456 * K24F.R0 τ * K24F.S0 z‖
      ≤ CQ * scale τ + 24 * CP * scale τ + CU * scale τ + 10368 * D * scale τ := by
    have h1 := norm_add_le (K24F.Q1 τ z + 24 * K24F.Phiref τ z - K24F.Uref τ z)
      (3456 * K24F.R0 τ * K24F.S0 z)
    have h3 := norm_sub_le (K24F.Q1 τ z + 24 * K24F.Phiref τ z) (K24F.Uref τ z)
    have h4 := norm_add_le (K24F.Q1 τ z) ((24 : ℂ) * K24F.Phiref τ z)
    linarith
  rw [K24F.Th0]
  calc ‖K24F.Q1 τ z + 24 * K24F.Phiref τ z - K24F.Uref τ z + 3456 * K24F.R0 τ * K24F.S0 z‖
      ≤ CQ * scale τ + 24 * CP * scale τ + CU * scale τ + 10368 * D * scale τ := hmain
    _ = (CQ + 24 * CP + CU + 10368 * D) * scale τ := by ring
    _ ≤ (CQ + 24 * CP + CU + 10368 * D + 1) * scale τ := by nlinarith [hs0]

end K24Fsm

/-! ## The deviation bounds for `Φ - Φref` and `Φ - Φref - q·Q⁽¹⁾` -/

/-- `Φ - Φref = O(scale τ · q)`. -/
theorem phi_sub_phiref_le : ∃ C : ℝ, 0 < C ∧ ∀ (τ z : ℍ), Funnel τ → 3 ≤ z.im →
    ‖K24F.Phi τ z - K24F.Phiref τ z‖ ≤ C * scale τ * ‖qParamFun z‖ := by
  obtain ⟨D, hD24, hDbd⟩ := K24F.tau_atom_bounds_D
  obtain ⟨A, hAp, hA⟩ := K24Fsm.zdev
  have hD0 : (0:ℝ) < D := by linarith
  refine ⟨D * A * 24240 + 1, by positivity, fun τ z hτ hz => ?_⟩
  obtain ⟨hdE4, hdE4c, hdSq, hdF, hdG2, hdE2, hdE4r, hdqd, hd1c, hdqd2, hdlow, hdinv,
    hE4inv, hE4up, hS0b⟩ := hA z hz
  obtain ⟨hr0, hr2, hR0, hr1, hj, hΔ, hΔinv⟩ := hDbd τ hτ
  have hq0 : (0:ℝ) ≤ ‖qParamFun z‖ := norm_nonneg _
  have hs0 : (0:ℝ) ≤ scale τ := (scale_pos τ).le
  have hE4ne : E4Fun z ≠ 0 := K24F.E4_ne_zero_three z hz
  have hr02 : ‖K24F.r0 τ + K24F.r2 τ‖ ≤ 2 * (D * scale τ) := by
    have h := norm_add_le (K24F.r0 τ) (K24F.r2 τ); linarith
  have hdev1 : ‖(E4Fun z - 1) - (E2S z ^ 2 - Small.S0c z ^ 2)‖ ≤ 2 * A * ‖qParamFun z‖ := by
    have h := norm_sub_le (E4Fun z - 1) (E2S z ^ 2 - Small.S0c z ^ 2)
    linarith
  have hdev2 : ‖12 * (E2S z ^ 2 - Small.S0c z ^ 2) - 12 * (E4Fun z - 1)‖
      ≤ 24 * A * ‖qParamFun z‖ := by
    have h := norm_sub_le ((12:ℂ) * (E2S z ^ 2 - Small.S0c z ^ 2)) ((12:ℂ) * (E4Fun z - 1))
    simp only [norm_mul, Complex.norm_ofNat] at h
    linarith
  have hdev3 : ‖8640 * (E4Fun z - 1) - 12096 * (E2S z ^ 2 - Small.S0c z ^ 2)‖
      ≤ 20736 * A * ‖qParamFun z‖ := by
    have h := norm_sub_le ((8640:ℂ) * (E4Fun z - 1)) ((12096:ℂ) * (E2S z ^ 2 - Small.S0c z ^ 2))
    simp only [norm_mul, Complex.norm_ofNat] at h
    linarith
  have h6r : ‖(6:ℂ) * (K24F.r0 τ + K24F.r2 τ)‖ ≤ 6 * (2 * (D * scale τ)) := by
    rw [norm_mul, Complex.norm_ofNat]
    exact mul_le_mul_of_nonneg_left hr02 (by norm_num)
  have hS1 : ‖(6:ℂ) * (K24F.r0 τ + K24F.r2 τ)
        * ((E4Fun z - 1) - (E2S z ^ 2 - Small.S0c z ^ 2))‖
      ≤ (6 * (2 * (D * scale τ))) * (2 * A * ‖qParamFun z‖) :=
    K24Fsm.norm_mul_le_mul h6r hdev1
  have hS2 : ‖K24F.R0 τ * (12 * (E2S z ^ 2 - Small.S0c z ^ 2) - 12 * (E4Fun z - 1))‖
      ≤ (D * scale τ) * (24 * A * ‖qParamFun z‖) := K24Fsm.norm_mul_le_mul hR0 hdev2
  have hS3 : ‖K24F.r1 τ * (8640 * (E4Fun z - 1) - 12096 * (E2S z ^ 2 - Small.S0c z ^ 2))‖
      ≤ (D * scale τ) * (20736 * A * ‖qParamFun z‖) := K24Fsm.norm_mul_le_mul hr1 hdev3
  have h3456 : ‖(3456:ℂ) * K24F.r1 τ‖ ≤ 3456 * (D * scale τ) := by
    rw [norm_mul, Complex.norm_ofNat]
    exact mul_le_mul_of_nonneg_left hr1 (by norm_num)
  have hS4 : ‖(3456:ℂ) * K24F.r1 τ * (E6Fun z * E2S z / E4Fun z - Small.S0c z)‖
      ≤ (3456 * (D * scale τ)) * (A * ‖qParamFun z‖) := K24Fsm.norm_mul_le_mul h3456 hdF
  have hsum : ‖(6:ℂ) * (K24F.r0 τ + K24F.r2 τ)
        * ((E4Fun z - 1) - (E2S z ^ 2 - Small.S0c z ^ 2))
      + K24F.R0 τ * (12 * (E2S z ^ 2 - Small.S0c z ^ 2) - 12 * (E4Fun z - 1))
      + K24F.r1 τ * (8640 * (E4Fun z - 1) - 12096 * (E2S z ^ 2 - Small.S0c z ^ 2))
      + (3456:ℂ) * K24F.r1 τ * (E6Fun z * E2S z / E4Fun z - Small.S0c z)‖
      ≤ ‖(6:ℂ) * (K24F.r0 τ + K24F.r2 τ)
            * ((E4Fun z - 1) - (E2S z ^ 2 - Small.S0c z ^ 2))‖
        + ‖K24F.R0 τ * (12 * (E2S z ^ 2 - Small.S0c z ^ 2) - 12 * (E4Fun z - 1))‖
        + ‖K24F.r1 τ * (8640 * (E4Fun z - 1) - 12096 * (E2S z ^ 2 - Small.S0c z ^ 2))‖
        + ‖(3456:ℂ) * K24F.r1 τ * (E6Fun z * E2S z / E4Fun z - Small.S0c z)‖ :=
    K24Fsm.norm_sum4_le
  have key : ‖(6:ℂ) * (K24F.r0 τ + K24F.r2 τ)
        * ((E4Fun z - 1) - (E2S z ^ 2 - Small.S0c z ^ 2))
      + K24F.R0 τ * (12 * (E2S z ^ 2 - Small.S0c z ^ 2) - 12 * (E4Fun z - 1))
      + K24F.r1 τ * (8640 * (E4Fun z - 1) - 12096 * (E2S z ^ 2 - Small.S0c z ^ 2))
      + (3456:ℂ) * K24F.r1 τ * (E6Fun z * E2S z / E4Fun z - Small.S0c z)‖
      ≤ D * A * 24240 * scale τ * ‖qParamFun z‖ := by
    calc ‖(6:ℂ) * (K24F.r0 τ + K24F.r2 τ)
          * ((E4Fun z - 1) - (E2S z ^ 2 - Small.S0c z ^ 2))
        + K24F.R0 τ * (12 * (E2S z ^ 2 - Small.S0c z ^ 2) - 12 * (E4Fun z - 1))
        + K24F.r1 τ * (8640 * (E4Fun z - 1) - 12096 * (E2S z ^ 2 - Small.S0c z ^ 2))
        + (3456:ℂ) * K24F.r1 τ * (E6Fun z * E2S z / E4Fun z - Small.S0c z)‖
        ≤ (6 * (2 * (D * scale τ))) * (2 * A * ‖qParamFun z‖)
          + (D * scale τ) * (24 * A * ‖qParamFun z‖)
          + (D * scale τ) * (20736 * A * ‖qParamFun z‖)
          + (3456 * (D * scale τ)) * (A * ‖qParamFun z‖) := by
          linarith [hsum, hS1, hS2, hS3, hS4]
      _ = D * A * 24240 * scale τ * ‖qParamFun z‖ := by ring
  have hgoal : ‖(6:ℂ) * (K24F.r0 τ + K24F.r2 τ)
        * ((E4Fun z - 1) - (E2S z ^ 2 - K24F.S0 z ^ 2))
      + K24F.R0 τ * (12 * (E2S z ^ 2 - K24F.S0 z ^ 2) - 12 * (E4Fun z - 1))
      + K24F.r1 τ * (8640 * (E4Fun z - 1) - 12096 * (E2S z ^ 2 - K24F.S0 z ^ 2))
      + (3456:ℂ) * K24F.r1 τ * (E6Fun z * E2S z / E4Fun z - K24F.S0 z)‖
      ≤ D * A * 24240 * scale τ * ‖qParamFun z‖ := by
    rw [K24Fsm.S0_eq_S0c]
    exact key
  rw [K24F.Phi_sub_Phiref_expanded τ z hE4ne]
  exact le_trans hgoal (by nlinarith [hs0, hq0, hAp, hD0])

/-- `B₂ = O(q²)`. -/
theorem b2_le : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 3 ≤ z.im →
    ‖K24F.B2 z‖ ≤ C * ‖qParamFun z‖ ^ 2 := by
  obtain ⟨A, hAp, hA⟩ := K24Fsm.zdev
  refine ⟨(6 * A + A ^ 2 + 48 * A + 576) + 1, by positivity, fun z hz => ?_⟩
  obtain ⟨hdE4, hdE4c, hdSq, hdF, hdG2, hdE2, hdE4r, hdqd, hd1c, hdqd2, hdlow, hdinv,
    hE4inv, hE4up, hS0b⟩ := hA z hz
  have hz1 : (1:ℝ) ≤ z.im := by linarith
  have hq0 : (0:ℝ) ≤ ‖qParamFun z‖ := norm_nonneg _
  have hq1 : ‖qParamFun z‖ ≤ 1 := norm_qParamFun_le_one z hz1
  have hq2 : ‖qParamFun z‖ ^ 2 ≤ ‖qParamFun z‖ := by nlinarith
  rw [K24F.B2]
  set X : ℂ := E2S z - Small.S0c z + 24 * qParamFun z with hX
  have hXb : ‖X‖ ≤ A * ‖qParamFun z‖ ^ 2 := by rw [hX]; exact hdE2
  have hS0K : ‖K24F.S0 z‖ ≤ 3 := hS0b
  have hS0 : ‖(2:ℂ) * K24F.S0 z‖ ≤ 6 := by
    rw [norm_mul, Complex.norm_ofNat]
    linarith
  have h1 : ‖(2:ℂ) * K24F.S0 z * X‖ ≤ 6 * A * ‖qParamFun z‖ ^ 2 := by
    have h := K24Fsm.norm_mul_le_mul hS0 hXb
    calc ‖(2:ℂ) * K24F.S0 z * X‖ ≤ 6 * (A * ‖qParamFun z‖ ^ 2) := h
      _ = 6 * A * ‖qParamFun z‖ ^ 2 := by ring
  have h2 : ‖X ^ 2‖ ≤ A ^ 2 * ‖qParamFun z‖ ^ 2 := by
    rw [norm_pow]
    have hX2 : ‖X‖ ^ 2 ≤ (A * ‖qParamFun z‖ ^ 2) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg X) hXb 2
    have hpt : ‖qParamFun z‖ ^ 2 ≤ 1 := by nlinarith [hq0, hq1]
    have hq4 : (‖qParamFun z‖ ^ 2) ^ 2 ≤ ‖qParamFun z‖ ^ 2 := by
      rw [pow_two]
      exact mul_le_of_le_one_right (by positivity) hpt
    have h3 : (A * ‖qParamFun z‖ ^ 2) ^ 2 ≤ A ^ 2 * ‖qParamFun z‖ ^ 2 := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left hq4 (by positivity)
    linarith
  have h3 : ‖(48:ℂ) * qParamFun z * X‖ ≤ 48 * A * ‖qParamFun z‖ ^ 2 := by
    have h48 : ‖(48:ℂ) * qParamFun z‖ ≤ 48 * ‖qParamFun z‖ := by
      rw [norm_mul, Complex.norm_ofNat]
    have h := K24Fsm.norm_mul_le_mul h48 hXb
    calc ‖(48:ℂ) * qParamFun z * X‖ ≤ (48 * ‖qParamFun z‖) * (A * ‖qParamFun z‖ ^ 2) := h
      _ = 48 * A * ‖qParamFun z‖ ^ 3 := by ring
      _ ≤ 48 * A * ‖qParamFun z‖ ^ 2 := by
          have hq3 : ‖qParamFun z‖ ^ 3 ≤ ‖qParamFun z‖ ^ 2 := by
            rw [pow_succ]
            exact mul_le_of_le_one_right (by positivity) hq1
          nlinarith [hq3, hAp]
  have h4 : ‖(576:ℂ) * qParamFun z ^ 2‖ ≤ 576 * ‖qParamFun z‖ ^ 2 := by
    rw [norm_mul, norm_pow, Complex.norm_ofNat]
  have hsum : ‖(2:ℂ) * K24F.S0 z * X + X ^ 2 - (48:ℂ) * qParamFun z * X
        + (576:ℂ) * qParamFun z ^ 2‖
      ≤ ‖(2:ℂ) * K24F.S0 z * X‖ + ‖X ^ 2‖ + ‖(48:ℂ) * qParamFun z * X‖
        + ‖(576:ℂ) * qParamFun z ^ 2‖ := by
    have h1' := norm_add_le ((2:ℂ) * K24F.S0 z * X + X ^ 2 - (48:ℂ) * qParamFun z * X)
      ((576:ℂ) * qParamFun z ^ 2)
    have h2' := norm_sub_le ((2:ℂ) * K24F.S0 z * X + X ^ 2) ((48:ℂ) * qParamFun z * X)
    have h3' := norm_add_le ((2:ℂ) * K24F.S0 z * X) (X ^ 2)
    linarith
  calc ‖(2:ℂ) * K24F.S0 z * X + X ^ 2 - (48:ℂ) * qParamFun z * X
        + (576:ℂ) * qParamFun z ^ 2‖
      ≤ 6 * A * ‖qParamFun z‖ ^ 2 + A ^ 2 * ‖qParamFun z‖ ^ 2
        + 48 * A * ‖qParamFun z‖ ^ 2 + 576 * ‖qParamFun z‖ ^ 2 := by
        linarith [hsum, h1, h2, h3, h4]
    _ = (6 * A + A ^ 2 + 48 * A + 576) * ‖qParamFun z‖ ^ 2 := by ring
    _ ≤ ((6 * A + A ^ 2 + 48 * A + 576) + 1) * ‖qParamFun z‖ ^ 2 := by
        nlinarith [hq0, hAp]

/-- `Φ - Φref - q·Q⁽¹⁾ = O(scale τ · q²)`. -/
theorem phi_sub_phiref_sub_le : ∃ C : ℝ, 0 < C ∧ ∀ (τ z : ℍ), Funnel τ → 3 ≤ z.im →
    ‖K24F.Phi τ z - K24F.Phiref τ z - qParamFun z * K24F.Q1 τ z‖
      ≤ C * scale τ * ‖qParamFun z‖ ^ 2 := by
  obtain ⟨D, hD24, hDbd⟩ := K24F.tau_atom_bounds_D
  obtain ⟨A, hAp, hA⟩ := K24Fsm.zdev
  obtain ⟨CB, hCBp, hCB⟩ := b2_le
  have hD0 : (0:ℝ) < D := by linarith
  refine ⟨D * (A + CB) * 12120 + 1, by positivity, fun τ z hτ hz => ?_⟩
  obtain ⟨hdE4, hdE4c, hdSq, hdF, hdG2, hdE2, hdE4r, hdqd, hd1c, hdqd2, hdlow, hdinv,
    hE4inv, hE4up, hS0b⟩ := hA z hz
  obtain ⟨hr0, hr2, hR0, hr1, hj, hΔ, hΔinv⟩ := hDbd τ hτ
  have hq0 : (0:ℝ) ≤ ‖qParamFun z‖ := norm_nonneg _
  have hs0 : (0:ℝ) ≤ scale τ := (scale_pos τ).le
  have hE4ne : E4Fun z ≠ 0 := K24F.E4_ne_zero_three z hz
  have hr02 : ‖K24F.r0 τ + K24F.r2 τ‖ ≤ 2 * (D * scale τ) := by
    have h := norm_add_le (K24F.r0 τ) (K24F.r2 τ); linarith
  have hB2 := hCB z hz
  have hdev1 : ‖(E4Fun z - 1 - 240 * qParamFun z) - K24F.B2 z‖
      ≤ (A + CB) * ‖qParamFun z‖ ^ 2 := by
    have h := norm_sub_le (E4Fun z - 1 - 240 * qParamFun z) (K24F.B2 z)
    linarith
  have hdev2 : ‖12 * K24F.B2 z - 12 * (E4Fun z - 1 - 240 * qParamFun z)‖
      ≤ 12 * (A + CB) * ‖qParamFun z‖ ^ 2 := by
    have h := norm_sub_le ((12:ℂ) * K24F.B2 z) ((12:ℂ) * (E4Fun z - 1 - 240 * qParamFun z))
    simp only [norm_mul, Complex.norm_ofNat] at h
    linarith
  have hdev3 : ‖8640 * (E4Fun z - 1 - 240 * qParamFun z) - 12096 * K24F.B2 z‖
      ≤ (8640 * A + 12096 * CB) * ‖qParamFun z‖ ^ 2 := by
    have h := norm_sub_le ((8640:ℂ) * (E4Fun z - 1 - 240 * qParamFun z)) ((12096:ℂ) * K24F.B2 z)
    simp only [norm_mul, Complex.norm_ofNat] at h
    linarith
  have hdev4 : ‖E6Fun z * E2S z / E4Fun z - Small.S0c z + 24 * qParamFun z
        + 744 * qParamFun z * Small.S0c z‖ ≤ A * ‖qParamFun z‖ ^ 2 := hdG2
  have h6r : ‖(6:ℂ) * (K24F.r0 τ + K24F.r2 τ)‖ ≤ 6 * (2 * (D * scale τ)) := by
    rw [norm_mul, Complex.norm_ofNat]
    exact mul_le_mul_of_nonneg_left hr02 (by norm_num)
  have hS1 : ‖(6:ℂ) * (K24F.r0 τ + K24F.r2 τ)
        * ((E4Fun z - 1 - 240 * qParamFun z) - K24F.B2 z)‖
      ≤ (6 * (2 * (D * scale τ))) * ((A + CB) * ‖qParamFun z‖ ^ 2) :=
    K24Fsm.norm_mul_le_mul h6r hdev1
  have hS2 : ‖K24F.R0 τ * (12 * K24F.B2 z - 12 * (E4Fun z - 1 - 240 * qParamFun z))‖
      ≤ (D * scale τ) * (12 * (A + CB) * ‖qParamFun z‖ ^ 2) :=
    K24Fsm.norm_mul_le_mul hR0 hdev2
  have hS3 : ‖K24F.r1 τ * (8640 * (E4Fun z - 1 - 240 * qParamFun z) - 12096 * K24F.B2 z)‖
      ≤ (D * scale τ) * ((8640 * A + 12096 * CB) * ‖qParamFun z‖ ^ 2) :=
    K24Fsm.norm_mul_le_mul hr1 hdev3
  have h3456 : ‖(3456:ℂ) * K24F.r1 τ‖ ≤ 3456 * (D * scale τ) := by
    rw [norm_mul, Complex.norm_ofNat]
    exact mul_le_mul_of_nonneg_left hr1 (by norm_num)
  have hS4 : ‖(3456:ℂ) * K24F.r1 τ * (E6Fun z * E2S z / E4Fun z - Small.S0c z
        + 24 * qParamFun z + 744 * qParamFun z * Small.S0c z)‖
      ≤ (3456 * (D * scale τ)) * (A * ‖qParamFun z‖ ^ 2) := K24Fsm.norm_mul_le_mul h3456 hdev4
  have hsum : ‖(6:ℂ) * (K24F.r0 τ + K24F.r2 τ)
        * ((E4Fun z - 1 - 240 * qParamFun z) - K24F.B2 z)
      + K24F.R0 τ * (12 * K24F.B2 z - 12 * (E4Fun z - 1 - 240 * qParamFun z))
      + K24F.r1 τ * (8640 * (E4Fun z - 1 - 240 * qParamFun z) - 12096 * K24F.B2 z)
      + (3456:ℂ) * K24F.r1 τ * (E6Fun z * E2S z / E4Fun z - Small.S0c z
          + 24 * qParamFun z + 744 * qParamFun z * Small.S0c z)‖
      ≤ ‖(6:ℂ) * (K24F.r0 τ + K24F.r2 τ)
            * ((E4Fun z - 1 - 240 * qParamFun z) - K24F.B2 z)‖
        + ‖K24F.R0 τ * (12 * K24F.B2 z - 12 * (E4Fun z - 1 - 240 * qParamFun z))‖
        + ‖K24F.r1 τ * (8640 * (E4Fun z - 1 - 240 * qParamFun z) - 12096 * K24F.B2 z)‖
        + ‖(3456:ℂ) * K24F.r1 τ * (E6Fun z * E2S z / E4Fun z - Small.S0c z
            + 24 * qParamFun z + 744 * qParamFun z * Small.S0c z)‖ := K24Fsm.norm_sum4_le
  have key : ‖(6:ℂ) * (K24F.r0 τ + K24F.r2 τ)
        * ((E4Fun z - 1 - 240 * qParamFun z) - K24F.B2 z)
      + K24F.R0 τ * (12 * K24F.B2 z - 12 * (E4Fun z - 1 - 240 * qParamFun z))
      + K24F.r1 τ * (8640 * (E4Fun z - 1 - 240 * qParamFun z) - 12096 * K24F.B2 z)
      + (3456:ℂ) * K24F.r1 τ * (E6Fun z * E2S z / E4Fun z - Small.S0c z
          + 24 * qParamFun z + 744 * qParamFun z * Small.S0c z)‖
      ≤ D * (A + CB) * 12120 * scale τ * ‖qParamFun z‖ ^ 2 := by
    calc ‖(6:ℂ) * (K24F.r0 τ + K24F.r2 τ)
          * ((E4Fun z - 1 - 240 * qParamFun z) - K24F.B2 z)
        + K24F.R0 τ * (12 * K24F.B2 z - 12 * (E4Fun z - 1 - 240 * qParamFun z))
        + K24F.r1 τ * (8640 * (E4Fun z - 1 - 240 * qParamFun z) - 12096 * K24F.B2 z)
        + (3456:ℂ) * K24F.r1 τ * (E6Fun z * E2S z / E4Fun z - Small.S0c z
            + 24 * qParamFun z + 744 * qParamFun z * Small.S0c z)‖
        ≤ (6 * (2 * (D * scale τ))) * ((A + CB) * ‖qParamFun z‖ ^ 2)
          + (D * scale τ) * (12 * (A + CB) * ‖qParamFun z‖ ^ 2)
          + (D * scale τ) * ((8640 * A + 12096 * CB) * ‖qParamFun z‖ ^ 2)
          + (3456 * (D * scale τ)) * (A * ‖qParamFun z‖ ^ 2) := by
          linarith [hsum, hS1, hS2, hS3, hS4]
      _ = D * (A + CB) * 12120 * scale τ * ‖qParamFun z‖ ^ 2 := by ring
  have hgoal : ‖(6:ℂ) * (K24F.r0 τ + K24F.r2 τ)
        * ((E4Fun z - 1 - 240 * qParamFun z) - K24F.B2 z)
      + K24F.R0 τ * (12 * K24F.B2 z - 12 * (E4Fun z - 1 - 240 * qParamFun z))
      + K24F.r1 τ * (8640 * (E4Fun z - 1 - 240 * qParamFun z) - 12096 * K24F.B2 z)
      + (3456:ℂ) * K24F.r1 τ * (E6Fun z * E2S z / E4Fun z - K24F.S0 z
          + 24 * qParamFun z + 744 * qParamFun z * K24F.S0 z)‖
      ≤ D * (A + CB) * 12120 * scale τ * ‖qParamFun z‖ ^ 2 := by
    rw [K24Fsm.S0_eq_S0c]
    exact key
  rw [K24F.Phi_sub_Phiref_sub_expanded τ z hE4ne]
  exact le_trans hgoal (by nlinarith [hs0, hq0, hAp, hCBp, hD0])

/-! ## The five remainder groups -/

theorem sm1_le : ∃ C : ℝ, 0 < C ∧ ∀ (τ z : ℍ) (t : ℝ), Funnel τ → τ.im + 1 ≤ t →
    (z : ℂ) = (t : ℂ) * Complex.I →
    ‖K24F.Sm1 τ z‖ ≤ C * scale τ * Real.exp (-(2 * Real.pi * (t - τ.im))) := by
  obtain ⟨D, hD24, hDbd⟩ := K24F.tau_atom_bounds_D
  obtain ⟨CΦ, hCΦp, hCΦ⟩ := phi_sub_phiref_le
  obtain ⟨CΦ2, hCΦ2p, hCΦ2⟩ := phi_sub_phiref_sub_le
  obtain ⟨CQ, hCQp, hCQ⟩ := K24Fsm.q1_le
  obtain ⟨A, hAp, hA⟩ := K24Fsm.zdev
  have hD0 : (0:ℝ) < D := by linarith
  refine ⟨D * CΦ + (27/8) * CQ * A + (27/8) * CΦ2 * A + 1, by positivity, ?_⟩
  intro τ z t hτ ht hz
  have ht3 : (3:ℝ) ≤ t := by have h2 := Funnel.im_two hτ; linarith
  have hzim : z.im = t := K24F.im_of_coe_eq_axis hz
  have hz3 : (3:ℝ) ≤ z.im := by rw [hzim]; exact ht3
  have hz1 : (1:ℝ) ≤ z.im := by linarith
  obtain ⟨hdE4, hdE4c, hdSq, hdF, hdG2, hdE2, hdE4r, hdqd, hd1c, hdqd2, hdlow, hdinv,
    hE4inv, hE4up, hS0b⟩ := hA z hz3
  obtain ⟨hr0, hr2, hR0, hr1, hj, hΔ, hΔinv⟩ := hDbd τ hτ
  have hs0 : (0:ℝ) < scale τ := scale_pos τ
  have hsle : (0:ℝ) ≤ scale τ := hs0.le
  have he0 : (0:ℝ) < Real.exp (-(2 * Real.pi * (t - τ.im))) := Real.exp_pos _
  have heq_exp : Real.exp (2 * Real.pi * τ.im) * ‖qParamFun z‖
      = Real.exp (-(2 * Real.pi * (t - τ.im))) := K24F.exp_mul_qnorm hzim
  have hqle : ‖qParamFun z‖ ≤ Real.exp (-(2 * Real.pi * (t - τ.im))) := by
    rw [K24F.qnorm_of_im hzim, Real.exp_le_exp]
    nlinarith [Real.pi_pos, τ.im_pos]
  have hq0 : (0:ℝ) ≤ ‖qParamFun z‖ := norm_nonneg _
  have hq1 : ‖qParamFun z‖ ≤ 1 := norm_qParamFun_le_one z hz1
  have hE4c : ‖E4Fun z ^ 3‖ ≤ 27/8 := by
    rw [norm_pow]
    have h2 := pow_le_pow_left₀ (norm_nonneg (E4Fun z)) hE4up 3
    have h3 : ((3:ℝ)/2)^3 = 27/8 := by norm_num
    linarith
  have hT1 : ‖jInvariantFun τ * (K24F.Phi τ z - K24F.Phiref τ z)‖
      ≤ D * CΦ * scale τ * Real.exp (-(2 * Real.pi * (t - τ.im))) := by
    have h := K24Fsm.norm_mul_le_mul hj (hCΦ τ z hτ hz3)
    calc ‖jInvariantFun τ * (K24F.Phi τ z - K24F.Phiref τ z)‖
        ≤ (D * Real.exp (2 * Real.pi * τ.im)) * (CΦ * scale τ * ‖qParamFun z‖) := h
      _ = D * CΦ * scale τ * (Real.exp (2 * Real.pi * τ.im) * ‖qParamFun z‖) := by ring
      _ = D * CΦ * scale τ * Real.exp (-(2 * Real.pi * (t - τ.im))) := by rw [heq_exp]
  have hT2 : ‖E4Fun z ^ 3 * K24F.Q1 τ z * (qParamFun z / DeltaFun z - 1)‖
      ≤ (27/8) * CQ * A * scale τ * Real.exp (-(2 * Real.pi * (t - τ.im))) := by
    have h1 : ‖E4Fun z ^ 3 * K24F.Q1 τ z‖ ≤ (27/8) * (CQ * scale τ) :=
      K24Fsm.norm_mul_le_mul hE4c (hCQ τ z hτ hz3)
    have h := K24Fsm.norm_mul_le_mul h1 hdqd
    calc ‖E4Fun z ^ 3 * K24F.Q1 τ z * (qParamFun z / DeltaFun z - 1)‖
        ≤ ((27/8) * (CQ * scale τ)) * (A * ‖qParamFun z‖) := h
      _ = (27/8) * CQ * A * scale τ * ‖qParamFun z‖ := by ring
      _ ≤ (27/8) * CQ * A * scale τ * Real.exp (-(2 * Real.pi * (t - τ.im))) :=
          mul_le_mul_of_nonneg_left hqle (by positivity)
  have hT3 : ‖E4Fun z ^ 3 * (K24F.Phi τ z - K24F.Phiref τ z - qParamFun z * K24F.Q1 τ z)
        * (DeltaFun z)⁻¹‖
      ≤ (27/8) * CΦ2 * A * scale τ * Real.exp (-(2 * Real.pi * (t - τ.im))) := by
    have h1 : ‖E4Fun z ^ 3 * (K24F.Phi τ z - K24F.Phiref τ z - qParamFun z * K24F.Q1 τ z)‖
        ≤ (27/8) * (CΦ2 * scale τ * ‖qParamFun z‖ ^ 2) :=
      K24Fsm.norm_mul_le_mul hE4c (hCΦ2 τ z hτ hz3)
    have h := K24Fsm.norm_mul_le_mul h1 hdinv
    calc ‖E4Fun z ^ 3 * (K24F.Phi τ z - K24F.Phiref τ z - qParamFun z * K24F.Q1 τ z)
          * (DeltaFun z)⁻¹‖
        ≤ ((27/8) * (CΦ2 * scale τ * ‖qParamFun z‖ ^ 2)) * (A * ‖qParamFun z‖⁻¹) := h
      _ = (27/8) * CΦ2 * A * scale τ * (‖qParamFun z‖ ^ 2 * ‖qParamFun z‖⁻¹) := by ring
      _ = (27/8) * CΦ2 * A * scale τ * ‖qParamFun z‖ := by rw [K24Fsm.qsq_mul_qinv]
      _ ≤ (27/8) * CΦ2 * A * scale τ * Real.exp (-(2 * Real.pi * (t - τ.im))) :=
          mul_le_mul_of_nonneg_left hqle (by positivity)
  rw [K24F.Sm1]
  rw [show E4Fun z ^ 3 * (K24F.Phi τ z - K24F.Phiref τ z - qParamFun z * K24F.Q1 τ z)
        / DeltaFun z
      = E4Fun z ^ 3 * (K24F.Phi τ z - K24F.Phiref τ z - qParamFun z * K24F.Q1 τ z)
        * (DeltaFun z)⁻¹ by ring]
  have hsub1 := norm_sub_le (jInvariantFun τ * (K24F.Phi τ z - K24F.Phiref τ z)
      - E4Fun z ^ 3 * K24F.Q1 τ z * (qParamFun z / DeltaFun z - 1))
      (E4Fun z ^ 3 * (K24F.Phi τ z - K24F.Phiref τ z - qParamFun z * K24F.Q1 τ z)
        * (DeltaFun z)⁻¹)
  have hsub2 := norm_sub_le (jInvariantFun τ * (K24F.Phi τ z - K24F.Phiref τ z))
      (E4Fun z ^ 3 * K24F.Q1 τ z * (qParamFun z / DeltaFun z - 1))
  calc ‖jInvariantFun τ * (K24F.Phi τ z - K24F.Phiref τ z)
        - E4Fun z ^ 3 * K24F.Q1 τ z * (qParamFun z / DeltaFun z - 1)
        - E4Fun z ^ 3 * (K24F.Phi τ z - K24F.Phiref τ z - qParamFun z * K24F.Q1 τ z)
          * (DeltaFun z)⁻¹‖
      ≤ D * CΦ * scale τ * Real.exp (-(2 * Real.pi * (t - τ.im)))
        + (27/8) * CQ * A * scale τ * Real.exp (-(2 * Real.pi * (t - τ.im)))
        + (27/8) * CΦ2 * A * scale τ * Real.exp (-(2 * Real.pi * (t - τ.im))) := by
        linarith [hsub1, hsub2, hT1, hT2, hT3]
    _ = (D * CΦ + (27/8) * CQ * A + (27/8) * CΦ2 * A) * scale τ
          * Real.exp (-(2 * Real.pi * (t - τ.im))) := by ring
    _ ≤ (D * CΦ + (27/8) * CQ * A + (27/8) * CΦ2 * A + 1) * scale τ
          * Real.exp (-(2 * Real.pi * (t - τ.im))) := by nlinarith [hsle, he0]

theorem sm2_le : ∃ C : ℝ, 0 < C ∧ ∀ (τ z : ℍ) (t : ℝ), Funnel τ → τ.im + 1 ≤ t →
    (z : ℂ) = (t : ℂ) * Complex.I →
    ‖K24F.Sm2 τ z‖ ≤ C * scale τ * Real.exp (-(2 * Real.pi * (t - τ.im))) := by
  obtain ⟨D, hD24, hDbd⟩ := K24F.tau_atom_bounds_D
  obtain ⟨CΦ, hCΦp, hCΦ⟩ := K24Fsm.phiref_le
  obtain ⟨A, hAp, hA⟩ := K24Fsm.zdev
  have hD0 : (0:ℝ) < D := by linarith
  refine ⟨D * CΦ * A + (27/8) * CΦ * A + 1, by positivity, ?_⟩
  intro τ z t hτ ht hz
  have ht3 : (3:ℝ) ≤ t := by have h2 := Funnel.im_two hτ; linarith
  have hzim : z.im = t := K24F.im_of_coe_eq_axis hz
  have hz3 : (3:ℝ) ≤ z.im := by rw [hzim]; exact ht3
  have hz1 : (1:ℝ) ≤ z.im := by linarith
  obtain ⟨hdE4, hdE4c, hdSq, hdF, hdG2, hdE2, hdE4r, hdqd, hd1c, hdqd2, hdlow, hdinv,
    hE4inv, hE4up, hS0b⟩ := hA z hz3
  obtain ⟨hr0, hr2, hR0, hr1, hj, hΔ, hΔinv⟩ := hDbd τ hτ
  have hs0 : (0:ℝ) < scale τ := scale_pos τ
  have hsle : (0:ℝ) ≤ scale τ := hs0.le
  have he0 : (0:ℝ) < Real.exp (-(2 * Real.pi * (t - τ.im))) := Real.exp_pos _
  have heq_exp : Real.exp (2 * Real.pi * τ.im) * ‖qParamFun z‖
      = Real.exp (-(2 * Real.pi * (t - τ.im))) := K24F.exp_mul_qnorm hzim
  have hqle : ‖qParamFun z‖ ≤ Real.exp (-(2 * Real.pi * (t - τ.im))) := by
    rw [K24F.qnorm_of_im hzim, Real.exp_le_exp]
    nlinarith [Real.pi_pos, τ.im_pos]
  have hq0 : (0:ℝ) ≤ ‖qParamFun z‖ := norm_nonneg _
  have hq1 : ‖qParamFun z‖ ≤ 1 := norm_qParamFun_le_one z hz1
  have hE4c : ‖E4Fun z ^ 3‖ ≤ 27/8 := by
    rw [norm_pow]
    have h2 := pow_le_pow_left₀ (norm_nonneg (E4Fun z)) hE4up 3
    have h3 : ((3:ℝ)/2)^3 = 27/8 := by norm_num
    linarith
  have hd1 : ‖K24F.d1 z‖ ≤ A * ‖qParamFun z‖ := hd1c
  have hT1 : ‖jInvariantFun τ * K24F.Phiref τ z * (1 - DeltaFun z / qParamFun z)‖
      ≤ D * CΦ * A * scale τ * Real.exp (-(2 * Real.pi * (t - τ.im))) := by
    have h1 : ‖jInvariantFun τ * K24F.Phiref τ z‖
        ≤ (D * Real.exp (2 * Real.pi * τ.im)) * (CΦ * scale τ) :=
      K24Fsm.norm_mul_le_mul hj (hCΦ τ z hτ hz3)
    have h := K24Fsm.norm_mul_le_mul h1 hdqd2
    calc ‖jInvariantFun τ * K24F.Phiref τ z * (1 - DeltaFun z / qParamFun z)‖
        ≤ ((D * Real.exp (2 * Real.pi * τ.im)) * (CΦ * scale τ)) * (A * ‖qParamFun z‖) := h
      _ = D * CΦ * A * scale τ * (Real.exp (2 * Real.pi * τ.im) * ‖qParamFun z‖) := by ring
      _ = D * CΦ * A * scale τ * Real.exp (-(2 * Real.pi * (t - τ.im))) := by rw [heq_exp]
  have hT2 : ‖E4Fun z ^ 3 * K24F.Phiref τ z * K24F.d1 z‖
      ≤ (27/8) * CΦ * A * scale τ * Real.exp (-(2 * Real.pi * (t - τ.im))) := by
    have h1 : ‖E4Fun z ^ 3 * K24F.Phiref τ z‖ ≤ (27/8) * (CΦ * scale τ) :=
      K24Fsm.norm_mul_le_mul hE4c (hCΦ τ z hτ hz3)
    have h := K24Fsm.norm_mul_le_mul h1 hd1
    calc ‖E4Fun z ^ 3 * K24F.Phiref τ z * K24F.d1 z‖
        ≤ ((27/8) * (CΦ * scale τ)) * (A * ‖qParamFun z‖) := h
      _ = (27/8) * CΦ * A * scale τ * ‖qParamFun z‖ := by ring
      _ ≤ (27/8) * CΦ * A * scale τ * Real.exp (-(2 * Real.pi * (t - τ.im))) :=
          mul_le_mul_of_nonneg_left hqle (by positivity)
  rw [K24F.Sm2]
  have hsub := norm_sub_le (jInvariantFun τ * K24F.Phiref τ z * (1 - DeltaFun z / qParamFun z))
    (E4Fun z ^ 3 * K24F.Phiref τ z * K24F.d1 z)
  calc ‖jInvariantFun τ * K24F.Phiref τ z * (1 - DeltaFun z / qParamFun z)
        - E4Fun z ^ 3 * K24F.Phiref τ z * K24F.d1 z‖
      ≤ D * CΦ * A * scale τ * Real.exp (-(2 * Real.pi * (t - τ.im)))
        + (27/8) * CΦ * A * scale τ * Real.exp (-(2 * Real.pi * (t - τ.im))) := by
        linarith [hsub, hT1, hT2]
    _ = (D * CΦ * A + (27/8) * CΦ * A) * scale τ
          * Real.exp (-(2 * Real.pi * (t - τ.im))) := by ring
    _ ≤ (D * CΦ * A + (27/8) * CΦ * A + 1) * scale τ
          * Real.exp (-(2 * Real.pi * (t - τ.im))) := by nlinarith [hsle, he0]

theorem sm3_le : ∃ C : ℝ, 0 < C ∧ ∀ (τ z : ℍ) (t : ℝ), Funnel τ → τ.im + 1 ≤ t →
    (z : ℂ) = (t : ℂ) * Complex.I →
    ‖K24F.Sm3 τ z‖ ≤ C * scale τ * Real.exp (-(2 * Real.pi * (t - τ.im))) := by
  obtain ⟨D, hD24, hDbd⟩ := K24F.tau_atom_bounds_D
  obtain ⟨A, hAp, hA⟩ := K24Fsm.zdev
  have hD0 : (0:ℝ) < D := by linarith
  refine ⟨13824 * A * D + 1, by positivity, ?_⟩
  intro τ z t hτ ht hz
  have ht3 : (3:ℝ) ≤ t := by have h2 := Funnel.im_two hτ; linarith
  have hzim : z.im = t := K24F.im_of_coe_eq_axis hz
  have hz3 : (3:ℝ) ≤ z.im := by rw [hzim]; exact ht3
  have hz1 : (1:ℝ) ≤ z.im := by linarith
  obtain ⟨hdE4, hdE4c, hdSq, hdF, hdG2, hdE2, hdE4r, hdqd, hd1c, hdqd2, hdlow, hdinv,
    hE4inv, hE4up, hS0b⟩ := hA z hz3
  obtain ⟨hr0, hr2, hR0, hr1, hj, hΔ, hΔinv⟩ := hDbd τ hτ
  have hs0 : (0:ℝ) < scale τ := scale_pos τ
  have hsle : (0:ℝ) ≤ scale τ := hs0.le
  have he0 : (0:ℝ) < Real.exp (-(2 * Real.pi * (t - τ.im))) := Real.exp_pos _
  have hqle : ‖qParamFun z‖ ≤ Real.exp (-(2 * Real.pi * (t - τ.im))) := by
    rw [K24F.qnorm_of_im hzim, Real.exp_le_exp]
    nlinarith [Real.pi_pos, τ.im_pos]
  have hq0 : (0:ℝ) ≤ ‖qParamFun z‖ := norm_nonneg _
  have hq1 : ‖qParamFun z‖ ≤ 1 := norm_qParamFun_le_one z hz1
  have hS0 : ‖K24F.S0 z‖ ≤ 3 := K24F.zS0_norm z hz1
  have hdF' : ‖E6Fun z * E2S z / E4Fun z - K24F.S0 z‖ ≤ A * ‖qParamFun z‖ := hdF
  have hbr : ‖K24F.S0 z * (E4Fun z ^ 3 - 1)
        - (E6Fun z * E2S z / E4Fun z - K24F.S0 z)‖ ≤ 4 * A * ‖qParamFun z‖ := by
    have h1 : ‖K24F.S0 z * (E4Fun z ^ 3 - 1)‖ ≤ 3 * (A * ‖qParamFun z‖) :=
      K24Fsm.norm_mul_le_mul hS0 hdE4c
    have hsub := norm_sub_le (K24F.S0 z * (E4Fun z ^ 3 - 1))
      (E6Fun z * E2S z / E4Fun z - K24F.S0 z)
    linarith
  have h3456 : ‖(3456:ℂ) * K24F.R0 τ‖ ≤ 3456 * (D * scale τ) := by
    rw [norm_mul, Complex.norm_ofNat]
    exact mul_le_mul_of_nonneg_left hR0 (by norm_num)
  have hmain : ‖(3456:ℂ) * K24F.R0 τ * (K24F.S0 z * (E4Fun z ^ 3 - 1)
        - (E6Fun z * E2S z / E4Fun z - K24F.S0 z))‖
      ≤ 13824 * A * D * scale τ * Real.exp (-(2 * Real.pi * (t - τ.im))) := by
    have h := K24Fsm.norm_mul_le_mul h3456 hbr
    calc ‖(3456:ℂ) * K24F.R0 τ * (K24F.S0 z * (E4Fun z ^ 3 - 1)
          - (E6Fun z * E2S z / E4Fun z - K24F.S0 z))‖
        ≤ (3456 * (D * scale τ)) * (4 * A * ‖qParamFun z‖) := h
      _ = 13824 * A * D * scale τ * ‖qParamFun z‖ := by ring
      _ ≤ 13824 * A * D * scale τ * Real.exp (-(2 * Real.pi * (t - τ.im))) :=
          mul_le_mul_of_nonneg_left hqle (by positivity)
  rw [K24F.Sm3_bracket]
  refine le_trans hmain ?_
  calc 13824 * A * D * scale τ * Real.exp (-(2 * Real.pi * (t - τ.im)))
      ≤ (13824 * A * D + 1) * scale τ * Real.exp (-(2 * Real.pi * (t - τ.im))) := by
        nlinarith [hsle, he0]

theorem sm4_le : ∃ C : ℝ, 0 < C ∧ ∀ (τ z : ℍ) (t : ℝ), Funnel τ → τ.im + 1 ≤ t →
    (z : ℂ) = (t : ℂ) * Complex.I →
    ‖K24F.Sm4 τ z‖ ≤ C * scale τ * Real.exp (-(2 * Real.pi * (t - τ.im))) := by
  obtain ⟨D, hD24, hDbd⟩ := K24F.tau_atom_bounds_D
  obtain ⟨A, hAp, hA⟩ := K24Fsm.zdev
  have hD0 : (0:ℝ) < D := by linarith
  refine ⟨20736 * A * D + 1, by positivity, ?_⟩
  intro τ z t hτ ht hz
  have ht3 : (3:ℝ) ≤ t := by have h2 := Funnel.im_two hτ; linarith
  have hzim : z.im = t := K24F.im_of_coe_eq_axis hz
  have hz3 : (3:ℝ) ≤ z.im := by rw [hzim]; exact ht3
  have hz1 : (1:ℝ) ≤ z.im := by linarith
  obtain ⟨hdE4, hdE4c, hdSq, hdF, hdG2, hdE2, hdE4r, hdqd, hd1c, hdqd2, hdlow, hdinv,
    hE4inv, hE4up, hS0b⟩ := hA z hz3
  obtain ⟨hr0, hr2, hR0, hr1, hj, hΔ, hΔinv⟩ := hDbd τ hτ
  have hs0 : (0:ℝ) < scale τ := scale_pos τ
  have hsle : (0:ℝ) ≤ scale τ := hs0.le
  have he0 : (0:ℝ) < Real.exp (-(2 * Real.pi * (t - τ.im))) := Real.exp_pos _
  have hqle : ‖qParamFun z‖ ≤ Real.exp (-(2 * Real.pi * (t - τ.im))) := by
    rw [K24F.qnorm_of_im hzim, Real.exp_le_exp]
    nlinarith [Real.pi_pos, τ.im_pos]
  have hq0 : (0:ℝ) ≤ ‖qParamFun z‖ := norm_nonneg _
  have hq1 : ‖qParamFun z‖ ≤ 1 := norm_qParamFun_le_one z hz1
  have hS0 : ‖K24F.S0 z‖ ≤ 3 := K24F.zS0_norm z hz1
  have hS0sq : ‖K24F.S0 z ^ 2‖ ≤ 9 := by
    rw [norm_pow]; nlinarith [hS0, norm_nonneg (K24F.S0 z)]
  have h1E4c : ‖1 - E4Fun z ^ 3‖ ≤ A * ‖qParamFun z‖ := by
    rw [show 1 - E4Fun z ^ 3 = -(E4Fun z ^ 3 - 1) by ring, norm_neg]
    exact hdE4c
  have h1728r0 : ‖(1728:ℂ) * K24F.r0 τ‖ ≤ 1728 * (D * scale τ) := by
    rw [norm_mul, Complex.norm_ofNat]
    exact mul_le_mul_of_nonneg_left hr0 (by norm_num)
  have h1728r2 : ‖(1728:ℂ) * K24F.r2 τ‖ ≤ 1728 * (D * scale τ) := by
    rw [norm_mul, Complex.norm_ofNat]
    exact mul_le_mul_of_nonneg_left hr2 (by norm_num)
  have hT1 : ‖(1728:ℂ) * K24F.r0 τ * (E2S z ^ 2 - K24F.S0 z ^ 2)‖
      ≤ 1728 * A * D * scale τ * Real.exp (-(2 * Real.pi * (t - τ.im))) := by
    have h := K24Fsm.norm_mul_le_mul h1728r0 hdSq
    calc ‖(1728:ℂ) * K24F.r0 τ * (E2S z ^ 2 - K24F.S0 z ^ 2)‖
        ≤ (1728 * (D * scale τ)) * (A * ‖qParamFun z‖) := h
      _ = 1728 * A * D * scale τ * ‖qParamFun z‖ := by ring
      _ ≤ 1728 * A * D * scale τ * Real.exp (-(2 * Real.pi * (t - τ.im))) :=
          mul_le_mul_of_nonneg_left hqle (by positivity)
  have hT2 : ‖(1728:ℂ) * K24F.r2 τ * (E4Fun z - 1)‖
      ≤ 1728 * A * D * scale τ * Real.exp (-(2 * Real.pi * (t - τ.im))) := by
    have h := K24Fsm.norm_mul_le_mul h1728r2 hdE4
    calc ‖(1728:ℂ) * K24F.r2 τ * (E4Fun z - 1)‖
        ≤ (1728 * (D * scale τ)) * (A * ‖qParamFun z‖) := h
      _ = 1728 * A * D * scale τ * ‖qParamFun z‖ := by ring
      _ ≤ 1728 * A * D * scale τ * Real.exp (-(2 * Real.pi * (t - τ.im))) :=
          mul_le_mul_of_nonneg_left hqle (by positivity)
  have hinner : ‖(1728:ℂ) * K24F.r0 τ * K24F.S0 z ^ 2 + (1728:ℂ) * K24F.r2 τ‖
      ≤ 1728 * (D * scale τ) * 9 + 1728 * (D * scale τ) := by
    have h1 : ‖(1728:ℂ) * K24F.r0 τ * K24F.S0 z ^ 2‖ ≤ (1728 * (D * scale τ)) * 9 :=
      K24Fsm.norm_mul_le_mul h1728r0 hS0sq
    have hadd := norm_add_le ((1728:ℂ) * K24F.r0 τ * K24F.S0 z ^ 2) ((1728:ℂ) * K24F.r2 τ)
    linarith
  have hT3 : ‖((1728:ℂ) * K24F.r0 τ * K24F.S0 z ^ 2 + (1728:ℂ) * K24F.r2 τ)
        * (1 - E4Fun z ^ 3)‖
      ≤ (1728 * (D * scale τ) * 9 + 1728 * (D * scale τ)) * (A * ‖qParamFun z‖) :=
    K24Fsm.norm_mul_le_mul hinner h1E4c
  rw [K24F.Sm4_split]
  have hsum : ‖(1728:ℂ) * K24F.r0 τ * (E2S z ^ 2 - K24F.S0 z ^ 2)
        + (1728:ℂ) * K24F.r2 τ * (E4Fun z - 1)
        + ((1728:ℂ) * K24F.r0 τ * K24F.S0 z ^ 2 + (1728:ℂ) * K24F.r2 τ)
          * (1 - E4Fun z ^ 3)‖
      ≤ ‖(1728:ℂ) * K24F.r0 τ * (E2S z ^ 2 - K24F.S0 z ^ 2)‖
        + ‖(1728:ℂ) * K24F.r2 τ * (E4Fun z - 1)‖
        + ‖((1728:ℂ) * K24F.r0 τ * K24F.S0 z ^ 2 + (1728:ℂ) * K24F.r2 τ)
            * (1 - E4Fun z ^ 3)‖ := K24Fsm.norm_sum3_le
  calc ‖(1728:ℂ) * K24F.r0 τ * (E2S z ^ 2 - K24F.S0 z ^ 2)
        + (1728:ℂ) * K24F.r2 τ * (E4Fun z - 1)
        + ((1728:ℂ) * K24F.r0 τ * K24F.S0 z ^ 2 + (1728:ℂ) * K24F.r2 τ)
          * (1 - E4Fun z ^ 3)‖
      ≤ 1728 * A * D * scale τ * Real.exp (-(2 * Real.pi * (t - τ.im)))
        + 1728 * A * D * scale τ * Real.exp (-(2 * Real.pi * (t - τ.im)))
        + (1728 * (D * scale τ) * 9 + 1728 * (D * scale τ)) * (A * ‖qParamFun z‖) := by
        linarith [hsum, hT1, hT2, hT3]
    _ ≤ 20736 * A * D * scale τ * Real.exp (-(2 * Real.pi * (t - τ.im))) := by
        have h3 : (1728 * (D * scale τ) * 9 + 1728 * (D * scale τ)) * (A * ‖qParamFun z‖)
            ≤ 17280 * A * D * scale τ * Real.exp (-(2 * Real.pi * (t - τ.im))) := by
          have hnn : (0:ℝ) ≤ 17280 * A * D * scale τ := by positivity
          calc (1728 * (D * scale τ) * 9 + 1728 * (D * scale τ)) * (A * ‖qParamFun z‖)
              = 17280 * A * D * scale τ * ‖qParamFun z‖ := by ring
            _ ≤ 17280 * A * D * scale τ * Real.exp (-(2 * Real.pi * (t - τ.im))) :=
                mul_le_mul_of_nonneg_left hqle hnn
        linarith [hT1, hT2, h3]
    _ ≤ (20736 * A * D + 1) * scale τ * Real.exp (-(2 * Real.pi * (t - τ.im))) := by
        nlinarith [hsle, he0]

theorem sm5_le : ∃ C : ℝ, 0 < C ∧ ∀ (τ z : ℍ) (t : ℝ), Funnel τ → τ.im + 1 ≤ t →
    (z : ℂ) = (t : ℂ) * Complex.I →
    ‖K24F.Sm5 τ z‖ ≤ C * scale τ * Real.exp (-(2 * Real.pi * (t - τ.im))) := by
  obtain ⟨D, hD24, hDbd⟩ := K24F.tau_atom_bounds_D
  obtain ⟨CΘ, hCΘp, hCΘ⟩ := K24Fsm.th0_le
  have hD0 : (0:ℝ) < D := by linarith
  refine ⟨2 * D * CΘ + 1, by positivity, ?_⟩
  intro τ z t hτ ht hz
  have ht3 : (3:ℝ) ≤ t := by have h2 := Funnel.im_two hτ; linarith
  have hzim : z.im = t := K24F.im_of_coe_eq_axis hz
  have hz3 : (3:ℝ) ≤ z.im := by rw [hzim]; exact ht3
  obtain ⟨hr0, hr2, hR0, hr1, hj, hΔ, hΔinv⟩ := hDbd τ hτ
  have hs0 : (0:ℝ) < scale τ := scale_pos τ
  have hsle : (0:ℝ) ≤ scale τ := hs0.le
  have he0 : (0:ℝ) < Real.exp (-(2 * Real.pi * (t - τ.im))) := Real.exp_pos _
  have hDz : ‖DeltaFun z‖ ≤ 2 * Real.exp (-(2 * Real.pi * t)) := by
    have h := DeltaFun_upper_sharp z (by linarith : 1 ≤ z.im)
    rwa [hzim] at h
  have hprod : ‖DeltaFun z * jInvariantFun τ‖
      ≤ 2 * D * Real.exp (-(2 * Real.pi * (t - τ.im))) := by
    have h := K24Fsm.norm_mul_le_mul hDz hj
    calc ‖DeltaFun z * jInvariantFun τ‖
        ≤ (2 * Real.exp (-(2 * Real.pi * t))) * (D * Real.exp (2 * Real.pi * τ.im)) := h
      _ = 2 * D * (Real.exp (-(2 * Real.pi * t)) * Real.exp (2 * Real.pi * τ.im)) := by ring
      _ = 2 * D * Real.exp (-(2 * Real.pi * (t - τ.im))) := by
          rw [show -(2 * Real.pi * (t - τ.im)) = -(2 * Real.pi * t) + 2 * Real.pi * τ.im by ring,
            Real.exp_add]
  rw [K24F.Sm5]
  rw [show -(DeltaFun z * jInvariantFun τ) * K24F.Th0 τ z
      = -((DeltaFun z * jInvariantFun τ) * K24F.Th0 τ z) by ring, norm_neg]
  have h := K24Fsm.norm_mul_le_mul hprod (hCΘ τ z hτ hz3)
  calc ‖(DeltaFun z * jInvariantFun τ) * K24F.Th0 τ z‖
      ≤ (2 * D * Real.exp (-(2 * Real.pi * (t - τ.im)))) * (CΘ * scale τ) := h
    _ = 2 * D * CΘ * scale τ * Real.exp (-(2 * Real.pi * (t - τ.im))) := by ring
    _ ≤ (2 * D * CΘ + 1) * scale τ * Real.exp (-(2 * Real.pi * (t - τ.im))) := by
        nlinarith [hsle, he0]

/-- **The five remainder groups of the `K₊^{(24)}` cusp expansion are `O(e^{-2π(t - Im τ)})`.**

For `τ` in the funnel `{τ ∈ 𝒟 : 2 ≤ Im τ}` and `z = i t` with `t ≥ Im τ + 1`,

  `‖Sm1 τ z + … + Sm5 τ z‖ ≤ C (scale τ)^N e^{-2π(t - Im τ)}`. -/
theorem K24F_sm_sum_bound :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        (z : ℂ) = (t : ℂ) * Complex.I →
        ‖Work.Asymptotics.K24F.Sm1 τ z + Work.Asymptotics.K24F.Sm2 τ z
          + Work.Asymptotics.K24F.Sm3 τ z + Work.Asymptotics.K24F.Sm4 τ z
          + Work.Asymptotics.K24F.Sm5 τ z‖
          ≤ C * (Work.Kernels.scale τ) ^ N
              * Real.exp (-(2 * Real.pi * (t - τ.im))) := by
  obtain ⟨C1, hC1p, hC1⟩ := sm1_le
  obtain ⟨C2, hC2p, hC2⟩ := sm2_le
  obtain ⟨C3, hC3p, hC3⟩ := sm3_le
  obtain ⟨C4, hC4p, hC4⟩ := sm4_le
  obtain ⟨C5, hC5p, hC5⟩ := sm5_le
  refine ⟨C1 + C2 + C3 + C4 + C5 + 1, 1, by positivity, by norm_num, ?_⟩
  intro τ z t hτ ht hz
  have h1 := hC1 τ z t hτ ht hz
  have h2 := hC2 τ z t hτ ht hz
  have h3 := hC3 τ z t hτ ht hz
  have h4 := hC4 τ z t hτ ht hz
  have h5 := hC5 τ z t hτ ht hz
  have hs0 : (0:ℝ) < scale τ := scale_pos τ
  have he0 : (0:ℝ) < Real.exp (-(2 * Real.pi * (t - τ.im))) := Real.exp_pos _
  have hsum : ‖Work.Asymptotics.K24F.Sm1 τ z + Work.Asymptotics.K24F.Sm2 τ z
        + Work.Asymptotics.K24F.Sm3 τ z + Work.Asymptotics.K24F.Sm4 τ z
        + Work.Asymptotics.K24F.Sm5 τ z‖
      ≤ ‖Work.Asymptotics.K24F.Sm1 τ z‖ + ‖Work.Asymptotics.K24F.Sm2 τ z‖
        + ‖Work.Asymptotics.K24F.Sm3 τ z‖ + ‖Work.Asymptotics.K24F.Sm4 τ z‖
        + ‖Work.Asymptotics.K24F.Sm5 τ z‖ := K24Fsm.norm_sum5_le
  rw [Real.rpow_one]
  calc ‖Work.Asymptotics.K24F.Sm1 τ z + Work.Asymptotics.K24F.Sm2 τ z
        + Work.Asymptotics.K24F.Sm3 τ z + Work.Asymptotics.K24F.Sm4 τ z
        + Work.Asymptotics.K24F.Sm5 τ z‖
      ≤ (C1 * scale τ * Real.exp (-(2 * Real.pi * (t - τ.im))))
        + (C2 * scale τ * Real.exp (-(2 * Real.pi * (t - τ.im))))
        + (C3 * scale τ * Real.exp (-(2 * Real.pi * (t - τ.im))))
        + (C4 * scale τ * Real.exp (-(2 * Real.pi * (t - τ.im))))
        + (C5 * scale τ * Real.exp (-(2 * Real.pi * (t - τ.im)))) := by
        linarith [hsum, h1, h2, h3, h4, h5]
    _ = (C1 + C2 + C3 + C4 + C5) * scale τ * Real.exp (-(2 * Real.pi * (t - τ.im))) := by ring
    _ ≤ (C1 + C2 + C3 + C4 + C5 + 1) * scale τ * Real.exp (-(2 * Real.pi * (t - τ.im))) := by
        nlinarith [hs0.le, he0.le]

end

end Work.Asymptotics
