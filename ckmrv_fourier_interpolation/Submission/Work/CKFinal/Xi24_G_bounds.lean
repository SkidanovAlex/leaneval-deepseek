import Mathlib
import Submission.Work.Asymptotics.ZAtomsThird.cusp_forms
import Submission.Work.Asymptotics.ZAtomsThird.first_order
import Submission.Work.Asymptotics.KPlusFunnel.ZFacts

namespace Work.CKFinal

set_option maxHeartbeats 1600000

open Work.Kernels

/-- `‖x^2 - 1‖ ≤ ‖x - 1‖ * (B + 1)` when `‖x‖ ≤ B`. -/
private lemma sq_sub_one_le {x : ℂ} {B : ℝ} (hB : ‖x‖ ≤ B) :
    ‖x ^ 2 - 1‖ ≤ ‖x - 1‖ * (B + 1) := by
  have hsplit : x ^ 2 - 1 = (x - 1) * (x + 1) := by ring
  rw [hsplit, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  calc ‖x + 1‖ ≤ ‖x‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    _ = ‖x‖ + 1 := by rw [norm_one]
    _ ≤ B + 1 := by linarith

/-- `‖x^3 - 1‖ ≤ ‖x - 1‖ * (B^2 + B + 1)` when `‖x‖ ≤ B`. -/
private lemma cube_sub_one_le {x : ℂ} {B : ℝ} (hB : ‖x‖ ≤ B) :
    ‖x ^ 3 - 1‖ ≤ ‖x - 1‖ * (B ^ 2 + B + 1) := by
  have hsplit : x ^ 3 - 1 = (x - 1) * (x ^ 2 + x + 1) := by ring
  have hb : ‖x ^ 2 + x + 1‖ ≤ B ^ 2 + B + 1 := by
    have h1 : ‖x ^ 2 + x + 1‖ ≤ ‖x ^ 2 + x‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    rw [norm_one] at h1
    have h2 : ‖x ^ 2 + x‖ ≤ ‖x ^ 2‖ + ‖x‖ := norm_add_le _ _
    have h3 : ‖x ^ 2‖ = ‖x‖ ^ 2 := norm_pow x 2
    have h4 : ‖x‖ ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (norm_nonneg x) hB 2
    linarith
  rw [hsplit, norm_mul]
  exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)

theorem Xi24_G_bounds :
    ∃ C : ℝ, 0 < C ∧
      (∀ τ z : UpperHalfPlane, (1 : ℝ) / 3 ≤ τ.im → (1 : ℝ) / 3 ≤ z.im →
        ‖Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ ^ 3
            * (5 * Work.Kernels.E4Fun z - 7 * Work.Kernels.E2Fun z ^ 2 + 2)
          + Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ * (Work.Kernels.E2Fun z ^ 2 - 1)
          + Work.Kernels.E2Fun τ ^ 2 * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ
            * (Work.Kernels.E4Fun z - 1)
          - 6 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2)‖
        ≤ C * ‖Work.Kernels.qParamFun τ‖ * ‖Work.Kernels.qParamFun z‖) ∧
      (∀ τ z : UpperHalfPlane, (1 : ℝ) / 3 ≤ τ.im → (1 : ℝ) / 3 ≤ z.im →
        ‖Work.Kernels.E4Fun τ ^ 3
            * (5 * Work.Kernels.E4Fun z - 7 * Work.Kernels.E2Fun z ^ 2 + 2)
          + 2 * Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ
            * (Work.Kernels.E4Fun z - 1)
          - 7 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2)‖
        ≤ C * ‖Work.Kernels.qParamFun τ‖ * ‖Work.Kernels.qParamFun z‖) := by
  obtain ⟨c2, hc2, h2⟩ := Work.Asymptotics.ZAtomsThird.E2Fun_two_term_third
  obtain ⟨c4, hc4, h4⟩ := Work.Asymptotics.ZAtomsThird.E4Fun_two_term_third
  obtain ⟨c6, hc6, h6⟩ := Work.Asymptotics.ZAtomsThird.E6Fun_two_term_third
  have hc2' : 0 ≤ c2 := hc2.le
  have hc4' : 0 ≤ c4 := hc4.le
  have hc6' : 0 ≤ c6 := hc6.le
  set U : ℝ := (24 + c2) + (240 + c4) + (504 + c6) + 1 with hU
  have hU0 : 0 ≤ U := by rw [hU]; positivity
  set T : ℝ := 1 + U with hT
  have hT0 : 0 ≤ T := by rw [hT]; linarith
  have hT1 : 1 ≤ T := by rw [hT]; linarith
  set W : ℝ := U * (T ^ 3 + T ^ 2 + T + 1) with hW
  set V : ℝ := U * (7 * T + 12) with hV
  have hW0 : 0 ≤ W := by rw [hW]; positivity
  have hV0 : 0 ≤ V := by rw [hV]; positivity
  have hdev : ∀ w : UpperHalfPlane, (1 : ℝ) / 3 ≤ w.im →
      ‖E2Fun w - 1‖ ≤ U * ‖qParamFun w‖ ∧
      ‖E4Fun w - 1‖ ≤ U * ‖qParamFun w‖ ∧
      ‖E6Fun w - 1‖ ≤ U * ‖qParamFun w‖ := by
    intro w hw
    have hqle : ‖qParamFun w‖ ≤ 1 / 3 := Work.Asymptotics.norm_qParam_le_third hw
    have hq0 : (0 : ℝ) ≤ ‖qParamFun w‖ := norm_nonneg _
    have hq2 : ‖qParamFun w‖ ^ 2 ≤ ‖qParamFun w‖ := by nlinarith
    have hU2 : (24 + c2) ≤ U := by rw [hU]; nlinarith [hc4', hc6']
    have hU4 : (240 + c4) ≤ U := by rw [hU]; nlinarith [hc2', hc6']
    have hU6 : (504 + c6) ≤ U := by rw [hU]; nlinarith [hc2', hc4']
    refine ⟨?_, ?_, ?_⟩
    · have h := h2 w hw
      have hsplit : E2Fun w - 1 = (E2Fun w - 1 + 24 * qParamFun w) - 24 * qParamFun w := by ring
      have hb : ‖E2Fun w - 1‖ ≤ (24 + c2) * ‖qParamFun w‖ := by
        rw [hsplit]
        calc ‖(E2Fun w - 1 + 24 * qParamFun w) - 24 * qParamFun w‖
            ≤ ‖E2Fun w - 1 + 24 * qParamFun w‖ + ‖(24 : ℂ) * qParamFun w‖ := norm_sub_le _ _
          _ ≤ c2 * ‖qParamFun w‖ ^ 2 + 24 * ‖qParamFun w‖ := by
              rw [norm_mul, Complex.norm_ofNat]; exact add_le_add h le_rfl
          _ ≤ (24 + c2) * ‖qParamFun w‖ := by nlinarith
      exact le_trans hb (mul_le_mul_of_nonneg_right hU2 hq0)
    · have h := h4 w hw
      have hsplit : E4Fun w - 1 = (E4Fun w - 1 - 240 * qParamFun w) + 240 * qParamFun w := by ring
      have hb : ‖E4Fun w - 1‖ ≤ (240 + c4) * ‖qParamFun w‖ := by
        rw [hsplit]
        calc ‖(E4Fun w - 1 - 240 * qParamFun w) + 240 * qParamFun w‖
            ≤ ‖E4Fun w - 1 - 240 * qParamFun w‖ + ‖(240 : ℂ) * qParamFun w‖ := norm_add_le _ _
          _ ≤ c4 * ‖qParamFun w‖ ^ 2 + 240 * ‖qParamFun w‖ := by
              rw [norm_mul, Complex.norm_ofNat]; exact add_le_add h le_rfl
          _ ≤ (240 + c4) * ‖qParamFun w‖ := by nlinarith
      exact le_trans hb (mul_le_mul_of_nonneg_right hU4 hq0)
    · have h := h6 w hw
      have hsplit : E6Fun w - 1 = (E6Fun w - 1 + 504 * qParamFun w) - 504 * qParamFun w := by ring
      have hb : ‖E6Fun w - 1‖ ≤ (504 + c6) * ‖qParamFun w‖ := by
        rw [hsplit]
        calc ‖(E6Fun w - 1 + 504 * qParamFun w) - 504 * qParamFun w‖
            ≤ ‖E6Fun w - 1 + 504 * qParamFun w‖ + ‖(504 : ℂ) * qParamFun w‖ := norm_sub_le _ _
          _ ≤ c6 * ‖qParamFun w‖ ^ 2 + 504 * ‖qParamFun w‖ := by
              rw [norm_mul, Complex.norm_ofNat]; exact add_le_add h le_rfl
          _ ≤ (504 + c6) * ‖qParamFun w‖ := by nlinarith
      exact le_trans hb (mul_le_mul_of_nonneg_right hU6 hq0)
  have hnorm : ∀ w : UpperHalfPlane, (1 : ℝ) / 3 ≤ w.im →
      ‖E2Fun w‖ ≤ T ∧ ‖E4Fun w‖ ≤ T ∧ ‖E6Fun w‖ ≤ T := by
    intro w hw
    have hq1 : ‖qParamFun w‖ ≤ 1 := by
      have hh := Work.Asymptotics.norm_qParam_le_third hw
      linarith
    obtain ⟨hu, hv, hw6⟩ := hdev w hw
    refine ⟨?_, ?_, ?_⟩
    · have he : E2Fun w = (E2Fun w - 1) + 1 := by ring
      rw [he]
      calc ‖(E2Fun w - 1) + 1‖ ≤ ‖E2Fun w - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
        _ ≤ U * ‖qParamFun w‖ + 1 := by rw [norm_one]; linarith
        _ ≤ T := by rw [hT]; nlinarith [hU0, hq1]
    · have he : E4Fun w = (E4Fun w - 1) + 1 := by ring
      rw [he]
      calc ‖(E4Fun w - 1) + 1‖ ≤ ‖E4Fun w - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
        _ ≤ U * ‖qParamFun w‖ + 1 := by rw [norm_one]; linarith
        _ ≤ T := by rw [hT]; nlinarith [hU0, hq1]
    · have he : E6Fun w = (E6Fun w - 1) + 1 := by ring
      rw [he]
      calc ‖(E6Fun w - 1) + 1‖ ≤ ‖E6Fun w - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
        _ ≤ U * ‖qParamFun w‖ + 1 := by rw [norm_one]; linarith
        _ ≤ T := by rw [hT]; nlinarith [hU0, hq1]
  have hWcoef : U * (T ^ 2 + T + 1) ≤ W := by
    rw [hW]; nlinarith [hU0, pow_nonneg hT0 3]
  have hVge : U * (T + 1) ≤ V := by rw [hV]; nlinarith [hU0, hT1]
  have hVge1 : U ≤ V := by rw [hV]; nlinarith [hU0, hT1]
  have htau_lb : ∀ τ : UpperHalfPlane, (1 : ℝ) / 3 ≤ τ.im →
      ‖E2Fun τ * E4Fun τ ^ 3 - 1‖ ≤ W * ‖qParamFun τ‖ ∧
      ‖E4Fun τ ^ 2 * E6Fun τ - 1‖ ≤ W * ‖qParamFun τ‖ ∧
      ‖E2Fun τ ^ 2 * E4Fun τ * E6Fun τ - 1‖ ≤ W * ‖qParamFun τ‖ ∧
      ‖E4Fun τ ^ 3 - 1‖ ≤ W * ‖qParamFun τ‖ ∧
      ‖E2Fun τ * E4Fun τ * E6Fun τ - 1‖ ≤ W * ‖qParamFun τ‖ := by
    intro τ hτ
    have hq10 : (0 : ℝ) ≤ ‖qParamFun τ‖ := norm_nonneg _
    obtain ⟨hu, hv, hw6⟩ := hdev τ hτ
    obtain ⟨ha, hb, hc⟩ := hnorm τ hτ
    have hsq4 : ‖E4Fun τ ^ 2 - 1‖ ≤ (U * ‖qParamFun τ‖) * (T + 1) := by
      calc ‖E4Fun τ ^ 2 - 1‖ ≤ ‖E4Fun τ - 1‖ * (T + 1) := sq_sub_one_le hb
        _ ≤ (U * ‖qParamFun τ‖) * (T + 1) := mul_le_mul_of_nonneg_right hv (by linarith)
    have hsq2 : ‖E2Fun τ ^ 2 - 1‖ ≤ (U * ‖qParamFun τ‖) * (T + 1) := by
      calc ‖E2Fun τ ^ 2 - 1‖ ≤ ‖E2Fun τ - 1‖ * (T + 1) := sq_sub_one_le ha
        _ ≤ (U * ‖qParamFun τ‖) * (T + 1) := mul_le_mul_of_nonneg_right hu (by linarith)
    have hcube4 : ‖E4Fun τ ^ 3 - 1‖ ≤ (U * ‖qParamFun τ‖) * (T ^ 2 + T + 1) := by
      calc ‖E4Fun τ ^ 3 - 1‖ ≤ ‖E4Fun τ - 1‖ * (T ^ 2 + T + 1) := cube_sub_one_le hb
        _ ≤ (U * ‖qParamFun τ‖) * (T ^ 2 + T + 1) := mul_le_mul_of_nonneg_right hv (by positivity)
    have h46 : ‖E4Fun τ * E6Fun τ - 1‖ ≤ (U * ‖qParamFun τ‖) * (T + 1) := by
      have hs : E4Fun τ * E6Fun τ - 1 = E4Fun τ * (E6Fun τ - 1) + (E4Fun τ - 1) := by ring
      rw [hs]
      calc ‖E4Fun τ * (E6Fun τ - 1) + (E4Fun τ - 1)‖
          ≤ ‖E4Fun τ * (E6Fun τ - 1)‖ + ‖E4Fun τ - 1‖ := norm_add_le _ _
        _ = ‖E4Fun τ‖ * ‖E6Fun τ - 1‖ + ‖E4Fun τ - 1‖ := by rw [norm_mul]
        _ ≤ T * (U * ‖qParamFun τ‖) + U * ‖qParamFun τ‖ :=
              add_le_add (mul_le_mul hb hw6 (norm_nonneg _) (by positivity)) hv
        _ = (U * ‖qParamFun τ‖) * (T + 1) := by ring
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have hs : E2Fun τ * E4Fun τ ^ 3 - 1
          = (E2Fun τ - 1) * E4Fun τ ^ 3 + (E4Fun τ ^ 3 - 1) := by ring
      rw [hs]
      calc ‖(E2Fun τ - 1) * E4Fun τ ^ 3 + (E4Fun τ ^ 3 - 1)‖
          ≤ ‖(E2Fun τ - 1) * E4Fun τ ^ 3‖ + ‖E4Fun τ ^ 3 - 1‖ := norm_add_le _ _
        _ = ‖E2Fun τ - 1‖ * ‖E4Fun τ‖ ^ 3 + ‖E4Fun τ ^ 3 - 1‖ := by rw [norm_mul, norm_pow]
        _ ≤ (U * ‖qParamFun τ‖) * T ^ 3 + (U * ‖qParamFun τ‖) * (T ^ 2 + T + 1) :=
              add_le_add (mul_le_mul hu (pow_le_pow_left₀ (norm_nonneg _) hb 3) (by positivity)
                (mul_nonneg hU0 hq10)) hcube4
        _ = W * ‖qParamFun τ‖ := by rw [hW]; ring
    · have hs : E4Fun τ ^ 2 * E6Fun τ - 1
          = E4Fun τ ^ 2 * (E6Fun τ - 1) + (E4Fun τ ^ 2 - 1) := by ring
      rw [hs]
      calc ‖E4Fun τ ^ 2 * (E6Fun τ - 1) + (E4Fun τ ^ 2 - 1)‖
          ≤ ‖E4Fun τ ^ 2 * (E6Fun τ - 1)‖ + ‖E4Fun τ ^ 2 - 1‖ := norm_add_le _ _
        _ = ‖E4Fun τ‖ ^ 2 * ‖E6Fun τ - 1‖ + ‖E4Fun τ ^ 2 - 1‖ := by rw [norm_mul, norm_pow]
        _ ≤ T ^ 2 * (U * ‖qParamFun τ‖) + (U * ‖qParamFun τ‖) * (T + 1) :=
              add_le_add (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hb 2) hw6 (norm_nonneg _)
                (by positivity)) hsq4
        _ = (U * (T ^ 2 + T + 1)) * ‖qParamFun τ‖ := by ring
        _ ≤ W * ‖qParamFun τ‖ := mul_le_mul_of_nonneg_right hWcoef hq10
    · have hs : E2Fun τ ^ 2 * E4Fun τ * E6Fun τ - 1
          = E2Fun τ ^ 2 * (E4Fun τ * E6Fun τ - 1) + (E2Fun τ ^ 2 - 1) := by ring
      rw [hs]
      calc ‖E2Fun τ ^ 2 * (E4Fun τ * E6Fun τ - 1) + (E2Fun τ ^ 2 - 1)‖
          ≤ ‖E2Fun τ ^ 2 * (E4Fun τ * E6Fun τ - 1)‖ + ‖E2Fun τ ^ 2 - 1‖ := norm_add_le _ _
        _ = ‖E2Fun τ‖ ^ 2 * ‖E4Fun τ * E6Fun τ - 1‖ + ‖E2Fun τ ^ 2 - 1‖ := by rw [norm_mul, norm_pow]
        _ ≤ T ^ 2 * ((U * ‖qParamFun τ‖) * (T + 1)) + (U * ‖qParamFun τ‖) * (T + 1) :=
              add_le_add (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) ha 2) h46 (norm_nonneg _)
                (by positivity)) hsq2
        _ = W * ‖qParamFun τ‖ := by rw [hW]; ring
    · calc ‖E4Fun τ ^ 3 - 1‖ ≤ (U * ‖qParamFun τ‖) * (T ^ 2 + T + 1) := hcube4
        _ = (U * (T ^ 2 + T + 1)) * ‖qParamFun τ‖ := by ring
        _ ≤ W * ‖qParamFun τ‖ := mul_le_mul_of_nonneg_right hWcoef hq10
    · have hs : E2Fun τ * E4Fun τ * E6Fun τ - 1
          = (E2Fun τ - 1) * (E4Fun τ * E6Fun τ) + (E4Fun τ * E6Fun τ - 1) := by ring
      rw [hs]
      have hb6 : ‖E4Fun τ * E6Fun τ‖ ≤ T * T := by
        rw [norm_mul]; exact mul_le_mul hb hc (norm_nonneg _) (by positivity)
      have hsub : ‖(E2Fun τ - 1) * (E4Fun τ * E6Fun τ)‖ ≤ (U * ‖qParamFun τ‖) * (T * T) := by
        rw [norm_mul]
        exact mul_le_mul hu hb6 (norm_nonneg _) (mul_nonneg hU0 hq10)
      calc ‖(E2Fun τ - 1) * (E4Fun τ * E6Fun τ) + (E4Fun τ * E6Fun τ - 1)‖
          ≤ ‖(E2Fun τ - 1) * (E4Fun τ * E6Fun τ)‖ + ‖E4Fun τ * E6Fun τ - 1‖ := norm_add_le _ _
        _ ≤ (U * ‖qParamFun τ‖) * (T * T) + (U * ‖qParamFun τ‖) * (T + 1) :=
              add_le_add hsub h46
        _ = (U * (T ^ 2 + T + 1)) * ‖qParamFun τ‖ := by ring
        _ ≤ W * ‖qParamFun τ‖ := mul_le_mul_of_nonneg_right hWcoef hq10
  have hzlb : ∀ z : UpperHalfPlane, (1 : ℝ) / 3 ≤ z.im →
      ‖5 * E4Fun z - 7 * E2Fun z ^ 2 + 2‖ ≤ V * ‖qParamFun z‖ ∧
      ‖E2Fun z ^ 2 - 1‖ ≤ V * ‖qParamFun z‖ ∧
      ‖E4Fun z - 1‖ ≤ V * ‖qParamFun z‖ := by
    intro z hz
    have hq20 : (0 : ℝ) ≤ ‖qParamFun z‖ := norm_nonneg _
    obtain ⟨pu, pv, pw⟩ := hdev z hz
    obtain ⟨pa, pb, pc⟩ := hnorm z hz
    have hsq2 : ‖E2Fun z ^ 2 - 1‖ ≤ (U * (T + 1)) * ‖qParamFun z‖ := by
      calc ‖E2Fun z ^ 2 - 1‖ ≤ ‖E2Fun z - 1‖ * (T + 1) := sq_sub_one_le pa
        _ ≤ (U * ‖qParamFun z‖) * (T + 1) := mul_le_mul_of_nonneg_right pu (by linarith)
        _ = (U * (T + 1)) * ‖qParamFun z‖ := by ring
    have hEE : ‖E4Fun z - E2Fun z ^ 2‖ ≤ (U * (T + 2)) * ‖qParamFun z‖ := by
      have hsplit : E4Fun z - E2Fun z ^ 2 = (E4Fun z - 1) - (E2Fun z ^ 2 - 1) := by ring
      rw [hsplit]
      calc ‖(E4Fun z - 1) - (E2Fun z ^ 2 - 1)‖
          ≤ ‖E4Fun z - 1‖ + ‖E2Fun z ^ 2 - 1‖ := norm_sub_le _ _
        _ ≤ U * ‖qParamFun z‖ + (U * (T + 1)) * ‖qParamFun z‖ := add_le_add pv hsq2
        _ = (U * (T + 2)) * ‖qParamFun z‖ := by ring
    refine ⟨?_, ?_, ?_⟩
    · have hsplit : 5 * E4Fun z - 7 * E2Fun z ^ 2 + 2
          = 5 * (E4Fun z - E2Fun z ^ 2) - 2 * (E2Fun z ^ 2 - 1) := by ring
      rw [hsplit]
      calc ‖5 * (E4Fun z - E2Fun z ^ 2) - 2 * (E2Fun z ^ 2 - 1)‖
          ≤ ‖(5 : ℂ) * (E4Fun z - E2Fun z ^ 2)‖ + ‖(2 : ℂ) * (E2Fun z ^ 2 - 1)‖ := norm_sub_le _ _
        _ = 5 * ‖E4Fun z - E2Fun z ^ 2‖ + 2 * ‖E2Fun z ^ 2 - 1‖ := by
              rw [norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_ofNat]
        _ ≤ 5 * ((U * (T + 2)) * ‖qParamFun z‖) + 2 * ((U * (T + 1)) * ‖qParamFun z‖) :=
              add_le_add (mul_le_mul_of_nonneg_left hEE (by norm_num))
                (mul_le_mul_of_nonneg_left hsq2 (by norm_num))
        _ = V * ‖qParamFun z‖ := by rw [hV]; ring
    · exact le_trans hsq2 (mul_le_mul_of_nonneg_right hVge hq20)
    · exact le_trans pv (mul_le_mul_of_nonneg_right hVge1 hq20)
  refine ⟨3 * W * V + 1, ?_, ?_, ?_⟩
  · have hm := mul_nonneg hW0 hV0; linarith
  · intro τ z hτ hz
    obtain ⟨hz1, hz2, hz3⟩ := hzlb z hz
    obtain ⟨ht1, ht2, ht3, _, _⟩ := htau_lb τ hτ
    have hq10 : (0 : ℝ) ≤ ‖qParamFun τ‖ := norm_nonneg _
    have hq20 : (0 : ℝ) ≤ ‖qParamFun z‖ := norm_nonneg _
    have hfac : E2Fun τ * E4Fun τ ^ 3 * (5 * E4Fun z - 7 * E2Fun z ^ 2 + 2)
          + E4Fun τ ^ 2 * E6Fun τ * (E2Fun z ^ 2 - 1)
          + E2Fun τ ^ 2 * E4Fun τ * E6Fun τ * (E4Fun z - 1)
          - 6 * (E4Fun z - E2Fun z ^ 2)
        = (E2Fun τ * E4Fun τ ^ 3 - 1) * (5 * E4Fun z - 7 * E2Fun z ^ 2 + 2)
          + (E4Fun τ ^ 2 * E6Fun τ - 1) * (E2Fun z ^ 2 - 1)
          + (E2Fun τ ^ 2 * E4Fun τ * E6Fun τ - 1) * (E4Fun z - 1) := by ring
    rw [hfac]
    have h1 : ‖(E2Fun τ * E4Fun τ ^ 3 - 1) * (5 * E4Fun z - 7 * E2Fun z ^ 2 + 2)‖
        ≤ (W * ‖qParamFun τ‖) * (V * ‖qParamFun z‖) := by
      rw [norm_mul]; exact mul_le_mul ht1 hz1 (norm_nonneg _) (mul_nonneg hW0 hq10)
    have h2 : ‖(E4Fun τ ^ 2 * E6Fun τ - 1) * (E2Fun z ^ 2 - 1)‖
        ≤ (W * ‖qParamFun τ‖) * (V * ‖qParamFun z‖) := by
      rw [norm_mul]; exact mul_le_mul ht2 hz2 (norm_nonneg _) (mul_nonneg hW0 hq10)
    have h3 : ‖(E2Fun τ ^ 2 * E4Fun τ * E6Fun τ - 1) * (E4Fun z - 1)‖
        ≤ (W * ‖qParamFun τ‖) * (V * ‖qParamFun z‖) := by
      rw [norm_mul]; exact mul_le_mul ht3 hz3 (norm_nonneg _) (mul_nonneg hW0 hq10)
    calc ‖(E2Fun τ * E4Fun τ ^ 3 - 1) * (5 * E4Fun z - 7 * E2Fun z ^ 2 + 2)
          + (E4Fun τ ^ 2 * E6Fun τ - 1) * (E2Fun z ^ 2 - 1)
          + (E2Fun τ ^ 2 * E4Fun τ * E6Fun τ - 1) * (E4Fun z - 1)‖
        ≤ (W * ‖qParamFun τ‖) * (V * ‖qParamFun z‖) + (W * ‖qParamFun τ‖) * (V * ‖qParamFun z‖)
          + (W * ‖qParamFun τ‖) * (V * ‖qParamFun z‖) := by
            have hA := norm_add_le
              ((E2Fun τ * E4Fun τ ^ 3 - 1) * (5 * E4Fun z - 7 * E2Fun z ^ 2 + 2)
                + (E4Fun τ ^ 2 * E6Fun τ - 1) * (E2Fun z ^ 2 - 1))
              ((E2Fun τ ^ 2 * E4Fun τ * E6Fun τ - 1) * (E4Fun z - 1))
            have hB := norm_add_le
              ((E2Fun τ * E4Fun τ ^ 3 - 1) * (5 * E4Fun z - 7 * E2Fun z ^ 2 + 2))
              ((E4Fun τ ^ 2 * E6Fun τ - 1) * (E2Fun z ^ 2 - 1))
            linarith [hA, hB, h1, h2, h3]
      _ = 3 * W * V * (‖qParamFun τ‖ * ‖qParamFun z‖) := by ring
      _ ≤ (3 * W * V + 1) * ‖qParamFun τ‖ * ‖qParamFun z‖ := by
            have hnn : 0 ≤ ‖qParamFun τ‖ * ‖qParamFun z‖ := mul_nonneg hq10 hq20
            nlinarith [hnn]
  · intro τ z hτ hz
    obtain ⟨hz1, _, hz3⟩ := hzlb z hz
    obtain ⟨_, _, _, ht4, ht5⟩ := htau_lb τ hτ
    have hq10 : (0 : ℝ) ≤ ‖qParamFun τ‖ := norm_nonneg _
    have hq20 : (0 : ℝ) ≤ ‖qParamFun z‖ := norm_nonneg _
    have hfac : E4Fun τ ^ 3 * (5 * E4Fun z - 7 * E2Fun z ^ 2 + 2)
          + 2 * E2Fun τ * E4Fun τ * E6Fun τ * (E4Fun z - 1)
          - 7 * (E4Fun z - E2Fun z ^ 2)
        = (E4Fun τ ^ 3 - 1) * (5 * E4Fun z - 7 * E2Fun z ^ 2 + 2)
          + 2 * (E2Fun τ * E4Fun τ * E6Fun τ - 1) * (E4Fun z - 1) := by ring
    rw [hfac]
    have h4 : ‖(E4Fun τ ^ 3 - 1) * (5 * E4Fun z - 7 * E2Fun z ^ 2 + 2)‖
        ≤ (W * ‖qParamFun τ‖) * (V * ‖qParamFun z‖) := by
      rw [norm_mul]; exact mul_le_mul ht4 hz1 (norm_nonneg _) (mul_nonneg hW0 hq10)
    have h5 : ‖2 * (E2Fun τ * E4Fun τ * E6Fun τ - 1) * (E4Fun z - 1)‖
        ≤ 2 * ((W * ‖qParamFun τ‖) * (V * ‖qParamFun z‖)) := by
      rw [norm_mul, norm_mul, Complex.norm_ofNat]
      have hα : 2 * ‖E2Fun τ * E4Fun τ * E6Fun τ - 1‖ ≤ 2 * (W * ‖qParamFun τ‖) :=
        mul_le_mul_of_nonneg_left ht5 (by norm_num)
      calc 2 * ‖E2Fun τ * E4Fun τ * E6Fun τ - 1‖ * ‖E4Fun z - 1‖
          ≤ (2 * (W * ‖qParamFun τ‖)) * (V * ‖qParamFun z‖) :=
              mul_le_mul hα hz3 (norm_nonneg _) (by positivity)
        _ = 2 * ((W * ‖qParamFun τ‖) * (V * ‖qParamFun z‖)) := by ring
    calc ‖(E4Fun τ ^ 3 - 1) * (5 * E4Fun z - 7 * E2Fun z ^ 2 + 2)
          + 2 * (E2Fun τ * E4Fun τ * E6Fun τ - 1) * (E4Fun z - 1)‖
        ≤ ‖(E4Fun τ ^ 3 - 1) * (5 * E4Fun z - 7 * E2Fun z ^ 2 + 2)‖
          + ‖2 * (E2Fun τ * E4Fun τ * E6Fun τ - 1) * (E4Fun z - 1)‖ := norm_add_le _ _
      _ ≤ (W * ‖qParamFun τ‖) * (V * ‖qParamFun z‖)
          + 2 * ((W * ‖qParamFun τ‖) * (V * ‖qParamFun z‖)) := add_le_add h4 h5
      _ = 3 * W * V * (‖qParamFun τ‖ * ‖qParamFun z‖) := by ring
      _ ≤ (3 * W * V + 1) * ‖qParamFun τ‖ * ‖qParamFun z‖ := by
            have hnn : 0 ≤ ‖qParamFun τ‖ * ‖qParamFun z‖ := mul_nonneg hq10 hq20
            nlinarith [hnn]

end Work.CKFinal
