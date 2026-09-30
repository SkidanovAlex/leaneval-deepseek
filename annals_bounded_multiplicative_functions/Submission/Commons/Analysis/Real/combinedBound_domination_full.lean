import Mathlib
import Submission.Commons.Analysis.Real.combinedBound_domination

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Real
open scoped Real
set_option maxHeartbeats 4000000

namespace CBDev

-- ===== the strengthened unit bound: the second summand also carries (log(s+3)+1)^3 =====

lemma cb_unit_full_aux {x s t : ℝ} (hx : Real.exp 16 ≤ x) (hs : s = Real.sqrt x)
    (ht : t = Real.log x) :
    (1 / (2 * Real.pi)) *
        (2 * ((1 + t) ^ 3 * (Real.log (s + 3) + 1) ^ 3 * x ^ (1 + 1 / t) * (1 / 2) / s) +
          8 * (1 + t) ^ 3 * x ^ (1 / 2 + 1 / t) * (Real.log (s + 3) + 1) ^ 3 *
            (Real.log (s / (1 / 2 + 1 / t)) + 1)) ≤
      1000000 * s * t ^ 10 := by
  have hsp : 0 < s := by rw [hs]; exact CBDev.sqrt_pos hx
  have hs0 : 0 ≤ s := le_of_lt hsp
  have htp : 0 < t := by rw [ht]; exact CBDev.log_pos hx
  have ht0 : 0 ≤ t := le_of_lt htp
  have ht1 : 1 ≤ t := by rw [ht]; exact CBDev.log_ge_one hx
  have hper := CBDev.perron hx
  have h1e : x ^ (1 + 1 / t) = Real.exp 1 * x := by simpa [ht] using hper.1
  have h2e : x ^ (1 / 2 + 1 / t) = Real.exp 1 * s := by
    simpa [ht, hs] using hper.2
  have hL1n0 : 0 ≤ Real.log (s + 3) + 1 := by simpa [hs] using CBDev.L1_nonneg hx
  have hL1c : (Real.log (s + 3) + 1) ^ 3 ≤ 8 * t ^ 3 := by
    simpa [hs, ht] using CBDev.L1_cube_le hx
  have hL2n0 : 0 ≤ Real.log (s / (1 / 2 + 1 / t)) + 1 := by
    simpa [hs, ht] using CBDev.L2_nonneg hx
  have hL2le3 : Real.log (s / (1 / 2 + 1 / t)) + 1 ≤ 3 * t := by
    simpa [hs, ht] using CBDev.L2_le_three_log hx
  have h1t3 : (1 + t) ^ 3 ≤ 8 * t ^ 3 := by
    have hsum : 1 + t ≤ 2 * t := by linarith
    have hcube : (1 + t) ^ 3 ≤ (2 * t) ^ 3 :=
      pow_le_pow_left₀ (by linarith : 0 ≤ 1 + t) hsum 3
    nlinarith [hcube]
  have hAn : 0 ≤ (1 + t) ^ 3 := pow_nonneg (by linarith : 0 ≤ 1 + t) 3
  have hL1cub : 0 ≤ (Real.log (s + 3) + 1) ^ 3 := pow_nonneg hL1n0 3
  have hb8n : 0 ≤ 8 * t ^ 3 := mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) (pow_nonneg ht0 3)
  have hc0 : 0 ≤ 1 + 8 * (Real.log (s / (1 / 2 + 1 / t)) + 1) := by
    have h8 : 0 ≤ 8 * (Real.log (s / (1 / 2 + 1 / t)) + 1) :=
      mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hL2n0
    linarith
  have h25 : 1 + 8 * (Real.log (s / (1 / 2 + 1 / t)) + 1) ≤ 25 * t := by
    have h8' : 8 * (Real.log (s / (1 / 2 + 1 / t)) + 1) ≤ 24 * t := by
      have h := mul_le_mul_of_nonneg_left hL2le3 (by norm_num : (0 : ℝ) ≤ 8)
      nlinarith
    nlinarith
  have hinner_eq :
      2 * ((1 + t) ^ 3 * (Real.log (s + 3) + 1) ^ 3 * x ^ (1 + 1 / t) * (1 / 2) / s) +
          8 * (1 + t) ^ 3 * x ^ (1 / 2 + 1 / t) * (Real.log (s + 3) + 1) ^ 3 *
            (Real.log (s / (1 / 2 + 1 / t)) + 1) =
        Real.exp 1 * s * (1 + t) ^ 3 * (Real.log (s + 3) + 1) ^ 3 *
          (1 + 8 * (Real.log (s / (1 / 2 + 1 / t)) + 1)) := by
    rw [h1e, h2e]
    have hxss : x = s * s := by
      rw [hs]
      exact (Real.mul_self_sqrt (CBDev.x_nonneg hx)).symm
    rw [hxss]
    field_simp [ne_of_gt hsp]
  have hpi0 : (0 : ℝ) < 2 * Real.pi := by positivity
  have hone : (1 / (2 * Real.pi)) ≤ 1 := by
    have hpi2 : (1 : ℝ) ≤ 2 * Real.pi := by
      have h := Real.pi_gt_three
      nlinarith
    exact (div_le_iff₀ hpi0).2 (by simpa using hpi2)
  -- nonnegativity of the factored bracket B = e·s·(1+t)^3·L1^3·(1+8L2)
  have hB0 : 0 ≤ Real.exp 1 * s * (1 + t) ^ 3 * (Real.log (s + 3) + 1) ^ 3 *
      (1 + 8 * (Real.log (s / (1 / 2 + 1 / t)) + 1)) := by
    have h1 : 0 ≤ (1 + t) ^ 3 * (Real.log (s + 3) + 1) ^ 3 := mul_nonneg hAn hL1cub
    have h2 : 0 ≤ s * ((1 + t) ^ 3 * (Real.log (s + 3) + 1) ^ 3) := mul_nonneg hs0 h1
    have h3 : 0 ≤ s * ((1 + t) ^ 3 * (Real.log (s + 3) + 1) ^ 3) *
        (1 + 8 * (Real.log (s / (1 / 2 + 1 / t)) + 1)) := mul_nonneg h2 hc0
    have h4 : 0 ≤ Real.exp 1 * (s * ((1 + t) ^ 3 * (Real.log (s + 3) + 1) ^ 3) *
        (1 + 8 * (Real.log (s / (1 / 2 + 1 / t)) + 1))) := mul_nonneg (le_of_lt (Real.exp_pos 1)) h3
    simpa [mul_assoc, mul_left_comm, mul_comm] using h4
  calc
    (1 / (2 * Real.pi)) *
        (2 * ((1 + t) ^ 3 * (Real.log (s + 3) + 1) ^ 3 * x ^ (1 + 1 / t) * (1 / 2) / s) +
          8 * (1 + t) ^ 3 * x ^ (1 / 2 + 1 / t) * (Real.log (s + 3) + 1) ^ 3 *
            (Real.log (s / (1 / 2 + 1 / t)) + 1))
        = (1 / (2 * Real.pi)) *
            (Real.exp 1 * s * (1 + t) ^ 3 * (Real.log (s + 3) + 1) ^ 3 *
              (1 + 8 * (Real.log (s / (1 / 2 + 1 / t)) + 1))) := by rw [hinner_eq]
    _ ≤ Real.exp 1 * s * (1 + t) ^ 3 * (Real.log (s + 3) + 1) ^ 3 *
          (1 + 8 * (Real.log (s / (1 / 2 + 1 / t)) + 1)) := by
          simpa using (mul_le_mul_of_nonneg_right hone hB0)
    _ ≤ 3 * s * (8 * t ^ 3) * (8 * t ^ 3) * (25 * t) := by
          have hAB : (1 + t) ^ 3 * (Real.log (s + 3) + 1) ^ 3 ≤
              (8 * t ^ 3) * (8 * t ^ 3) :=
            mul_le_mul h1t3 hL1c hL1cub hb8n
          have hABc : ((1 + t) ^ 3 * (Real.log (s + 3) + 1) ^ 3) *
              (1 + 8 * (Real.log (s / (1 / 2 + 1 / t)) + 1)) ≤
              ((8 * t ^ 3) * (8 * t ^ 3)) * (25 * t) :=
            mul_le_mul hAB h25 hc0 (mul_nonneg hb8n hb8n)
          have hTail : s * (((1 + t) ^ 3 * (Real.log (s + 3) + 1) ^ 3) *
              (1 + 8 * (Real.log (s / (1 / 2 + 1 / t)) + 1))) ≤
              s * (((8 * t ^ 3) * (8 * t ^ 3)) * (25 * t)) :=
            mul_le_mul_of_nonneg_left hABc hs0
          have hTail0 : 0 ≤ s * (((1 + t) ^ 3 * (Real.log (s + 3) + 1) ^ 3) *
              (1 + 8 * (Real.log (s / (1 / 2 + 1 / t)) + 1))) :=
            mul_nonneg hs0 (mul_nonneg (mul_nonneg hAn hL1cub) hc0)
          have he3 : Real.exp 1 ≤ 3 := le_of_lt Real.exp_one_lt_three
          calc
            Real.exp 1 * s * (1 + t) ^ 3 * (Real.log (s + 3) + 1) ^ 3 *
                (1 + 8 * (Real.log (s / (1 / 2 + 1 / t)) + 1))
                = Real.exp 1 * (s * (((1 + t) ^ 3 * (Real.log (s + 3) + 1) ^ 3) *
                    (1 + 8 * (Real.log (s / (1 / 2 + 1 / t)) + 1)))) := by ring
            _ ≤ 3 * (s * (((8 * t ^ 3) * (8 * t ^ 3)) * (25 * t))) := by
                  exact mul_le_mul he3 hTail hTail0 (by norm_num : (0 : ℝ) ≤ 3)
            _ = 3 * s * (8 * t ^ 3) * (8 * t ^ 3) * (25 * t) := by ring
    _ = 4800 * s * t ^ 7 := by ring
    _ ≤ 1000000 * s * t ^ 10 := by
          have ht7 : t ^ 7 ≤ t ^ 10 := pow_le_pow_right₀ ht1 (by norm_num : (7 : ℕ) ≤ 10)
          have hstn : 0 ≤ s * t ^ 10 := mul_nonneg hs0 (pow_nonneg ht0 10)
          have h1 : 4800 * (s * t ^ 7) ≤ 4800 * (s * t ^ 10) := by
            have hst7 : 0 ≤ s * t ^ 7 := mul_nonneg hs0 (pow_nonneg ht0 7)
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ht7 hs0) (by norm_num : (0 : ℝ) ≤ 4800)
          have h2 : 4800 * (s * t ^ 10) ≤ 1000000 * (s * t ^ 10) := by
            exact mul_le_mul_of_nonneg_right (by norm_num : (4800 : ℝ) ≤ 1000000) hstn
          calc
            4800 * s * t ^ 7 = 4800 * (s * t ^ 7) := by ring
            _ ≤ 4800 * (s * t ^ 10) := h1
            _ ≤ 1000000 * (s * t ^ 10) := h2
            _ = 1000000 * s * t ^ 10 := by ring

lemma cb_unit_full_le {x : ℝ} (hx : Real.exp 16 ≤ x) :
    (1 / (2 * Real.pi)) *
        (2 * ((1 + Real.log x) ^ 3 * (Real.log (Real.sqrt x + 3) + 1) ^ 3 *
            x ^ (1 + 1 / Real.log x) * (1 / 2) / Real.sqrt x) +
          8 * (1 + Real.log x) ^ 3 * x ^ (1 / 2 + 1 / Real.log x) *
            (Real.log (Real.sqrt x + 3) + 1) ^ 3 *
            (Real.log (Real.sqrt x / (1 / 2 + 1 / Real.log x)) + 1)) ≤
      1000000 * Real.sqrt x * (Real.log x) ^ 10 := by
  exact cb_unit_full_aux hx rfl rfl

end CBDev

namespace Commons.Analysis.Real

theorem combinedBound_domination_full {C P x : ℝ} (hC : 0 < C) (hP : 0 ≤ P)
    (hx : Real.exp 16 ≤ x) :
    P * (x * (Real.log x) ^ 2 / Real.sqrt x + Real.log x) +
        (1 / (2 * Real.pi)) *
          (2 * (C * (1 + Real.log x) ^ 3 * (Real.log (Real.sqrt x + 3) + 1) ^ 3 *
              (x : ℝ) ^ (1 + 1 / Real.log x) * (1 / 2) / Real.sqrt x) +
           8 * C * (1 + Real.log x) ^ 3 * (x : ℝ) ^ (1 / 2 + 1 / Real.log x) *
             (Real.log (Real.sqrt x + 3) + 1) ^ 3 *
             (Real.log (Real.sqrt x / (1 / 2 + 1 / Real.log x)) + 1)) ≤
      (P + C + 1) * 1000000 * Real.sqrt x * (Real.log x) ^ 10 := by
  have hA := CBDev.cb_A_le_R0 hx
  have hU := CBDev.cb_unit_full_le hx
  have hC0 : 0 ≤ C := le_of_lt hC
  have hR0 : 0 ≤ 1000000 * Real.sqrt x * (Real.log x) ^ 10 := by
    positivity
  have hA' : P * (x * (Real.log x) ^ 2 / Real.sqrt x + Real.log x) ≤
      P * (1000000 * Real.sqrt x * (Real.log x) ^ 10) :=
    mul_le_mul_of_nonneg_left hA hP
  have hU' : C * ((1 / (2 * Real.pi)) *
        (2 * ((1 + Real.log x) ^ 3 * (Real.log (Real.sqrt x + 3) + 1) ^ 3 *
            x ^ (1 + 1 / Real.log x) * (1 / 2) / Real.sqrt x) +
          8 * (1 + Real.log x) ^ 3 * x ^ (1 / 2 + 1 / Real.log x) *
            (Real.log (Real.sqrt x + 3) + 1) ^ 3 *
            (Real.log (Real.sqrt x / (1 / 2 + 1 / Real.log x)) + 1))) ≤
      C * (1000000 * Real.sqrt x * (Real.log x) ^ 10) :=
    mul_le_mul_of_nonneg_left hU hC0
  calc
    P * (x * (Real.log x) ^ 2 / Real.sqrt x + Real.log x) +
        (1 / (2 * Real.pi)) *
          (2 * (C * (1 + Real.log x) ^ 3 * (Real.log (Real.sqrt x + 3) + 1) ^ 3 *
              (x : ℝ) ^ (1 + 1 / Real.log x) * (1 / 2) / Real.sqrt x) +
           8 * C * (1 + Real.log x) ^ 3 * (x : ℝ) ^ (1 / 2 + 1 / Real.log x) *
             (Real.log (Real.sqrt x + 3) + 1) ^ 3 *
             (Real.log (Real.sqrt x / (1 / 2 + 1 / Real.log x)) + 1))
        = P * (x * (Real.log x) ^ 2 / Real.sqrt x + Real.log x) +
          C * ((1 / (2 * Real.pi)) *
            (2 * ((1 + Real.log x) ^ 3 * (Real.log (Real.sqrt x + 3) + 1) ^ 3 *
                x ^ (1 + 1 / Real.log x) * (1 / 2) / Real.sqrt x) +
              8 * (1 + Real.log x) ^ 3 * x ^ (1 / 2 + 1 / Real.log x) *
                (Real.log (Real.sqrt x + 3) + 1) ^ 3 *
                (Real.log (Real.sqrt x / (1 / 2 + 1 / Real.log x)) + 1))) := by ring
    _ ≤ P * (1000000 * Real.sqrt x * (Real.log x) ^ 10) +
        C * (1000000 * Real.sqrt x * (Real.log x) ^ 10) := add_le_add hA' hU'
    _ = (P + C) * (1000000 * Real.sqrt x * (Real.log x) ^ 10) := by ring
    _ ≤ (P + C + 1) * (1000000 * Real.sqrt x * (Real.log x) ^ 10) := by
      exact mul_le_mul_of_nonneg_right (by linarith) hR0
    _ = (P + C + 1) * 1000000 * Real.sqrt x * (Real.log x) ^ 10 := by ring

end Commons.Analysis.Real
