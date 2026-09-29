import Mathlib

set_option maxHeartbeats 1000000

namespace Work.TMC16Core.Core

/-- Monotonicity of `t ↦ log (1 + c*t)/t` in the form used by the Ten Martini C16
arithmetic: for `0 < c`, `0 < y`, `0 < ß`, `0 ≤ m ≤ y`, `m ≤ ß` we have
`log (1 + c*y) * m ≤ y * log (1 + c*ß)`. -/
lemma log_one_add_mul_le {c y ß m : ℝ} (hc : 0 < c) (hy : 0 < y) (hß : 0 < ß)
    (hm : 0 ≤ m) (hmy : m ≤ y) (hmß : m ≤ ß) :
    Real.log (1 + c * y) * m ≤ y * Real.log (1 + c * ß) := by
  have hy1 : (0:ℝ) < 1 + c*y := by nlinarith
  have hß1 : (0:ℝ) < 1 + c*ß := by nlinarith
  rcases lt_trichotomy y ß with h | h | h
  · have hlog : Real.log (1 + c*y) ≤ Real.log (1 + c*ß) := Real.log_le_log hy1 (by nlinarith)
    have h0 : 0 ≤ Real.log (1 + c*y) := Real.log_nonneg (by nlinarith)
    calc Real.log (1 + c*y) * m ≤ Real.log (1 + c*y) * y := mul_le_mul_of_nonneg_left hmy h0
      _ ≤ Real.log (1 + c*ß) * y := mul_le_mul_of_nonneg_right hlog hy.le
      _ = y * Real.log (1 + c*ß) := by ring
  · rw [h]
    have h0 : 0 ≤ Real.log (1 + c*ß) := Real.log_nonneg (by nlinarith)
    calc Real.log (1 + c*ß) * m ≤ Real.log (1 + c*ß) * ß := mul_le_mul_of_nonneg_left hmß h0
      _ = ß * Real.log (1 + c*ß) := by ring
  · have hyß : 0 < y - ß := by linarith
    have hkey : ß * Real.log (1 + c*y) ≤ y * Real.log (1 + c*ß) := by
      have hfac : 1 + c*y = (1 + c*ß) * (1 + c*(y-ß)/(1+c*ß)) := by
        field_simp
        ring
      have hpos2 : (0:ℝ) < 1 + c*(y-ß)/(1+c*ß) := by
        have hc1 : 0 < c*(y-ß)/(1+c*ß) := by
          apply div_pos (mul_pos hc hyß); linarith
        linarith
      rw [hfac, Real.log_mul (ne_of_gt hß1) (ne_of_gt hpos2)]
      have hle1 : Real.log (1 + c*(y-ß)/(1+c*ß)) ≤ c*(y-ß)/(1+c*ß) := by
        have := Real.log_le_sub_one_of_pos hpos2; linarith
      have hle2 : c*ß/(1+c*ß) ≤ Real.log (1 + c*ß) := by
        have hh := Real.one_sub_inv_le_log_of_pos hß1
        have he : (1:ℝ) - (1 + c*ß)⁻¹ = c*ß/(1+c*ß) := by field_simp; ring
        rw [he] at hh; exact hh
      have hstep : ß * Real.log (1 + c*(y-ß)/(1+c*ß)) ≤ (y - ß) * Real.log (1 + c*ß) := by
        calc ß * Real.log (1 + c*(y-ß)/(1+c*ß)) ≤ ß * (c*(y-ß)/(1+c*ß)) :=
              mul_le_mul_of_nonneg_left hle1 hß.le
          _ = (y-ß)*(c*ß/(1+c*ß)) := by ring_nf
          _ ≤ (y-ß)*Real.log (1+c*ß) := mul_le_mul_of_nonneg_left hle2 (by linarith)
      nlinarith [hstep]
    calc Real.log (1 + c*y)*m ≤ Real.log (1 + c*y)*ß :=
          mul_le_mul_of_nonneg_left hmß (Real.log_nonneg (by nlinarith))
      _ = ß * Real.log (1 + c*y) := by ring
      _ ≤ y * Real.log (1 + c*ß) := hkey

/-- For `2 ≤ L` and `0 ≤ x ≤ 11/10`:
`log (1 + 10*π*x/3) ≤ π*x + log (2*L^2/π)`. -/
lemma log_one_add_pi_mul_le {L : ℕ} (hL : 2 ≤ L) {x : ℝ} (hx0 : 0 ≤ x) (_hx1 : x ≤ 11/10) :
    Real.log (1 + 10 * Real.pi * x / 3) ≤ Real.pi * x + Real.log (2 * (L:ℝ)^2 / Real.pi) := by
  have hπ0 : (0:ℝ) < Real.pi := Real.pi_pos
  have hπu : Real.pi < 3.1416 := Real.pi_lt_d4
  have hd_l : (0.6931471803:ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hd_u : Real.log 2 < (0.6931471808:ℝ) := Real.log_two_lt_d9
  have hL2 : (2:ℝ) ≤ (L:ℝ) := by exact_mod_cast hL
  -- log(10/3) bound
  have hlog10_3 : Real.log (10/3) ≤ 2 * Real.log 2 - 1/6 := by
    have hmul : Real.log (10/3) = Real.log 4 + Real.log (5/6) := by
      rw [← Real.log_mul (by norm_num : (4:ℝ) ≠ 0) (by norm_num : (5/6:ℝ) ≠ 0)]; norm_num
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      have h4 : (4:ℝ) = 2^2 := by norm_num
      rw [h4, Real.log_pow]; norm_num
    rw [hmul, hlog4]
    have h : Real.log (5/6) ≤ (5/6:ℝ) - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    norm_num at h ⊢
    linarith
  -- log pi bound
  have hlogpi : Real.log Real.pi ≤ 2 * Real.log 2 - 1/5 := by
    have hlog5 : 2 * Real.log 2 + 1/5 ≤ Real.log 5 := by
      have hmul : Real.log 5 = Real.log 4 + Real.log (5/4) := by
        rw [← Real.log_mul (by norm_num : (4:ℝ) ≠ 0) (by norm_num : (5/4:ℝ) ≠ 0)]; norm_num
      have hlog4 : Real.log 4 = 2 * Real.log 2 := by
        have h4 : (4:ℝ) = 2^2 := by norm_num
        rw [h4, Real.log_pow]; norm_num
      rw [hmul, hlog4]
      have h : 1 - (5/4:ℝ)⁻¹ ≤ Real.log (5/4) := Real.one_sub_inv_le_log_of_pos (by norm_num)
      norm_num at h ⊢
      linarith
    have hlt : Real.pi ≤ 16/5 := by have h := Real.pi_lt_d4; norm_num at h; linarith
    have h1 : Real.log Real.pi ≤ Real.log (16/5) := Real.log_le_log Real.pi_pos hlt
    have hmul : Real.log (16/5) = Real.log 16 - Real.log 5 := by
      rw [Real.log_div (by norm_num : (16:ℝ) ≠ 0) (by norm_num : (5:ℝ) ≠ 0)]
    have h16 : Real.log 16 = 4 * Real.log 2 := by
      have h4 : (16:ℝ) = 2^4 := by norm_num
      rw [h4, Real.log_pow]; norm_num
    rw [hmul, h16] at h1
    linarith
  -- decompose the log
  have hpos : 0 < Real.pi * x + 3/10 := by nlinarith
  have hdec : Real.log (1 + 10 * Real.pi * x / 3) = Real.log (10/3) + Real.log (Real.pi * x + 3/10) := by
    have harg : 1 + 10 * Real.pi * x / 3 = (10/3) * (Real.pi * x + 3/10) := by ring
    rw [harg, Real.log_mul (by norm_num : (10/3:ℝ) ≠ 0) (ne_of_gt hpos)]
  have hlogarg : Real.log (Real.pi * x + 3/10) ≤ Real.pi * x - 7/10 := by
    have h := Real.log_le_sub_one_of_pos hpos; linarith
  -- bound log(2 L^2 / pi)
  have h2L2 : Real.log 2 + 1/5 ≤ Real.log (2 * (L:ℝ)^2 / Real.pi) := by
    have hmono : Real.log (8/Real.pi) ≤ Real.log (2 * (L:ℝ)^2 / Real.pi) := by
      apply Real.log_le_log
      · positivity
      · have h8L : (8:ℝ) ≤ 2 * (L:ℝ)^2 := by nlinarith
        exact div_le_div_of_nonneg_right h8L (le_of_lt Real.pi_pos)
    have h8 : Real.log (8/Real.pi) = 3 * Real.log 2 - Real.log Real.pi := by
      rw [Real.log_div (by norm_num : (8:ℝ) ≠ 0) (by positivity : (Real.pi:ℝ) ≠ 0)]
      have h8' : Real.log (8:ℝ) = 3 * Real.log 2 := by
        have h : (8:ℝ) = 2^3 := by norm_num
        rw [h, Real.log_pow]; norm_num
      rw [h8']
    linarith
  linarith [hdec, hlogarg, hlog10_3, h2L2, hd_u]

end Work.TMC16Core.Core

namespace Work.TMC16Core.Core

theorem final_arith {L : ℕ} (hL : 2 ≤ L) {η β m : ℝ}
    (hη0 : 0 < η) (hηL : η * (L : ℝ) ≤ 11 / 10)
    (hβ1 : β ≤ 2 * (L : ℝ) * (1 + Real.log (L : ℝ)))
    (hβ2 : β ≤ ((L : ℝ) - 1) * (L : ℝ))
    (hm0 : 0 ≤ m) (hm1 : m ≤ 2 * Real.pi * η * (L : ℝ)) (hm2 : m ≤ (L : ℝ) - 1) :
    (2 * Real.pi * η * β + Real.log (1 + 20 * Real.pi * η * (L : ℝ) / 3) * m
        + Real.pi * η * (L : ℝ) ≤ 32 * (η * (L : ℝ)) * Real.log (L : ℝ)) ∧
    (2 * Real.pi * η * β + Real.log (1 + 20 * Real.pi * η * (L : ℝ) / 3) * m
        + Real.log (1 + 10 * Real.pi * η * (L : ℝ) / 3)
        ≤ Real.log (L : ℝ) + 32 * (η * (L : ℝ)) * Real.log (L : ℝ)
          + Real.log (2 * (L : ℝ) / Real.pi)) := by
  have hπ0 : (0:ℝ) < Real.pi := Real.pi_pos
  have hπu : Real.pi < 3.1416 := Real.pi_lt_d4
  have hπl : (3.1415:ℝ) < Real.pi := Real.pi_gt_d4
  have hd_l : (0.6931471803:ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hd_u : Real.log 2 < (0.6931471808:ℝ) := Real.log_two_lt_d9
  have hL2 : (2:ℝ) ≤ (L:ℝ) := by exact_mod_cast hL
  have hLpos : (0:ℝ) < (L:ℝ) := by linarith
  have hxnn : (0:ℝ) ≤ η * (L:ℝ) := le_of_lt (mul_pos hη0 hLpos)
  -- elementary log bounds
  have hlog3 : Real.log 2 + 1/3 ≤ Real.log 3 := by
    have hmul : Real.log 3 = Real.log 2 + Real.log (3/2) := by
      rw [← Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by norm_num : (3/2:ℝ) ≠ 0)]
      norm_num
    rw [hmul]
    have h : 1 - (3/2:ℝ)⁻¹ ≤ Real.log (3/2) := Real.one_sub_inv_le_log_of_pos (by norm_num)
    norm_num at h ⊢
    linarith
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    have h : (4:ℝ) = 2^2 := by norm_num
    rw [h, Real.log_pow]; norm_num
  have hlog5 : 2 * Real.log 2 + 1/5 ≤ Real.log 5 := by
    have hmul : Real.log 5 = Real.log 4 + Real.log (5/4) := by
      rw [← Real.log_mul (by norm_num : (4:ℝ) ≠ 0) (by norm_num : (5/4:ℝ) ≠ 0)]; norm_num
    rw [hmul, hlog4]
    have h : 1 - (5/4:ℝ)⁻¹ ≤ Real.log (5/4) := Real.one_sub_inv_le_log_of_pos (by norm_num)
    norm_num at h ⊢
    linarith
  have hlog6 : 2 * Real.log 2 + 1/3 ≤ Real.log 6 := by
    have hmul : Real.log 6 = Real.log 4 + Real.log (3/2) := by
      rw [← Real.log_mul (by norm_num : (4:ℝ) ≠ 0) (by norm_num : (3/2:ℝ) ≠ 0)]; norm_num
    rw [hmul, hlog4]
    have h : 1 - (3/2:ℝ)⁻¹ ≤ Real.log (3/2) := Real.one_sub_inv_le_log_of_pos (by norm_num)
    norm_num at h ⊢
    linarith
  have hlog7 : 3 * Real.log 2 - 1/7 ≤ Real.log 7 := by
    have hmul : Real.log 7 = Real.log 8 + Real.log (7/8) := by
      rw [← Real.log_mul (by norm_num : (8:ℝ) ≠ 0) (by norm_num : (7/8:ℝ) ≠ 0)]; norm_num
    have h8 : Real.log 8 = 3 * Real.log 2 := by
      have h : (8:ℝ) = 2^3 := by norm_num
      rw [h, Real.log_pow]; norm_num
    rw [hmul, h8]
    have h : 1 - (7/8:ℝ)⁻¹ ≤ Real.log (7/8) := Real.one_sub_inv_le_log_of_pos (by norm_num)
    norm_num at h ⊢
    linarith
  have hlog13_3 : Real.log (13/3) ≤ 2 * Real.log 2 + 1/12 := by
    have hmul : Real.log (13/3) = Real.log 4 + Real.log (13/12) := by
      rw [← Real.log_mul (by norm_num : (4:ℝ) ≠ 0) (by norm_num : (13/12:ℝ) ≠ 0)]; norm_num
    rw [hmul, hlog4]
    have h : Real.log (13/12) ≤ (13/12:ℝ) - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    norm_num at h ⊢
    linarith
  -- bound used for conjunct 2
  have hh : Real.log (1 + 10 * Real.pi * η * (L:ℝ) / 3)
      ≤ Real.pi * (η * (L:ℝ)) + Real.log (2 * (L:ℝ)^2 / Real.pi) := by
    have h := log_one_add_pi_mul_le (L := L) hL (x := η*(L:ℝ)) hxnn hηL
    rw [show (10:ℝ)*Real.pi*(η*(L:ℝ))/3 = 10*Real.pi*η*(L:ℝ)/3 by ring] at h
    exact h
  -- beta bounds
  have hb1 : 2 * Real.pi * η * β ≤ 4 * Real.pi * (η * (L:ℝ)) * (1 + Real.log (L:ℝ)) := by
    have h2πη : (0:ℝ) ≤ 2 * Real.pi * η := by positivity
    have h1 := mul_le_mul_of_nonneg_left hβ1 h2πη
    calc 2 * Real.pi * η * β ≤ 2 * Real.pi * η * (2 * (L:ℝ) * (1 + Real.log (L:ℝ))) := h1
      _ = 4 * Real.pi * (η * (L:ℝ)) * (1 + Real.log (L:ℝ)) := by ring
  have hb2 : 2 * Real.pi * η * β ≤ 2 * Real.pi * (η * (L:ℝ)) * ((L:ℝ) - 1) := by
    have h2πη : (0:ℝ) ≤ 2 * Real.pi * η := by positivity
    have h1 := mul_le_mul_of_nonneg_left hβ2 h2πη
    calc 2 * Real.pi * η * β ≤ 2 * Real.pi * η * (((L:ℝ) - 1) * (L:ℝ)) := h1
      _ = 2 * Real.pi * (η * (L:ℝ)) * ((L:ℝ) - 1) := by ring
  -- T bound, written in the exact syntactic shape of the goal
  have hT : Real.log (1 + 20 * Real.pi * η * (L:ℝ) / 3) * m
      ≤ 2 * Real.pi * (η * (L:ℝ)) * Real.log (1 + 10 * ((L:ℝ) - 1) / 3) := by
    have hy : (0:ℝ) < 2 * Real.pi * (η * (L:ℝ)) := by positivity
    have hß : (0:ℝ) < (L:ℝ) - 1 := by linarith
    have hm1' : m ≤ 2 * Real.pi * (η * (L:ℝ)) := by
      have h : 2 * Real.pi * η * (L:ℝ) = 2 * Real.pi * (η * (L:ℝ)) := by ring
      linarith [hm1, h]
    have key := log_one_add_mul_le (c := (10:ℝ)/3) (by norm_num) hy hß hm0 hm1' hm2
    rw [show (10:ℝ)/3 * (2 * Real.pi * (η * (L:ℝ))) = 20 * Real.pi * η * (L:ℝ) / 3 by ring,
        show (10:ℝ)/3 * ((L:ℝ) - 1) = 10 * ((L:ℝ) - 1) / 3 by ring] at key
    exact key
  have hmain1 : 2 * Real.pi * η * β + Real.log (1 + 20 * Real.pi * η * (L : ℝ) / 3) * m
        + Real.pi * η * (L : ℝ) ≤ 32 * (η * (L : ℝ)) * Real.log (L : ℝ) := by
    by_cases hL6 : L ≤ 6
    · interval_cases L <;> norm_num at *
      · -- L = 2
        have hTx := hT.trans (mul_le_mul_of_nonneg_left hlog13_3 (by positivity))
        have hnum : 2 * Real.pi + 2 * Real.pi * (2 * Real.log 2 + 1/12) + Real.pi
            ≤ 32 * Real.log 2 := by
          nlinarith [hπ0, hπu, hπl, hd_l, hd_u]
        have hnum' := mul_le_mul_of_nonneg_left hnum (by positivity : (0:ℝ) ≤ η * (2:ℝ))
        linarith [hb2, hTx, hnum']
      · -- L = 3
        have hlogb : Real.log (23/3) ≤ 2 * Real.log 2 + Real.log 3 := by
          have h1 : Real.log (23/3) ≤ Real.log 12 := Real.log_le_log (by norm_num) (by norm_num)
          have h2 : Real.log 12 = 2 * Real.log 2 + Real.log 3 := by
            rw [show (12:ℝ) = 4*3 by norm_num,
                Real.log_mul (by norm_num : (4:ℝ) ≠ 0) (by norm_num : (3:ℝ) ≠ 0), hlog4]
          linarith [h1, h2]
        have hTx := hT.trans (mul_le_mul_of_nonneg_left hlogb (by positivity))
        have hnum : 2 * Real.pi * 2 + 2 * Real.pi * (2 * Real.log 2 + Real.log 3) + Real.pi
            ≤ 32 * Real.log 3 := by
          nlinarith [hπ0, hπu, hπl, hd_l, hd_u, hlog3]
        have hnum' := mul_le_mul_of_nonneg_left hnum (by positivity : (0:ℝ) ≤ η * (3:ℝ))
        linarith [hb2, hTx, hnum']
      · -- L = 4
        have hlogb : Real.log 11 ≤ 4 * Real.log 2 := by
          have h1 : Real.log 11 ≤ Real.log 16 := Real.log_le_log (by norm_num) (by norm_num)
          have h2 : Real.log 16 = 4 * Real.log 2 := by
            have h : (16:ℝ) = 2^4 := by norm_num
            rw [h, Real.log_pow]; norm_num
          linarith [h1, h2]
        have hTx := hT.trans (mul_le_mul_of_nonneg_left hlogb (by positivity))
        have hnum : 2 * Real.pi * 3 + 2 * Real.pi * (4 * Real.log 2) + Real.pi
            ≤ 32 * Real.log 4 := by
          nlinarith [hπ0, hπu, hπl, hd_l, hd_u, hlog4]
        have hnum' := mul_le_mul_of_nonneg_left hnum (by positivity : (0:ℝ) ≤ η * (4:ℝ))
        linarith [hb2, hTx, hnum']
      · -- L = 5
        have hlogb : Real.log (43/3) ≤ 4 * Real.log 2 := by
          have h1 : Real.log (43/3) ≤ Real.log 16 := Real.log_le_log (by norm_num) (by norm_num)
          have h2 : Real.log 16 = 4 * Real.log 2 := by
            have h : (16:ℝ) = 2^4 := by norm_num
            rw [h, Real.log_pow]; norm_num
          linarith [h1, h2]
        have hTx := hT.trans (mul_le_mul_of_nonneg_left hlogb (by positivity))
        have hnum : 2 * Real.pi * 4 + 2 * Real.pi * (4 * Real.log 2) + Real.pi
            ≤ 32 * Real.log 5 := by
          nlinarith [hπ0, hπu, hπl, hd_l, hd_u, hlog5]
        have hnum' := mul_le_mul_of_nonneg_left hnum (by positivity : (0:ℝ) ≤ η * (5:ℝ))
        linarith [hb2, hTx, hnum']
      · -- L = 6
        have hlogb : Real.log (53/3) ≤ 2 * Real.log 2 + Real.log 6 := by
          have h1 : Real.log (53/3) ≤ Real.log 24 := Real.log_le_log (by norm_num) (by norm_num)
          have h2 : Real.log 24 = 2 * Real.log 2 + Real.log 6 := by
            rw [show (24:ℝ) = 4*6 by norm_num,
                Real.log_mul (by norm_num : (4:ℝ) ≠ 0) (by norm_num : (6:ℝ) ≠ 0), hlog4]
          linarith [h1, h2]
        have hTx := hT.trans (mul_le_mul_of_nonneg_left hlogb (by positivity))
        have hnum : 2 * Real.pi * 5 + 2 * Real.pi * (2 * Real.log 2 + Real.log 6) + Real.pi
            ≤ 32 * Real.log 6 := by
          nlinarith [hπ0, hπu, hπl, hd_l, hd_u, hlog6]
        have hnum' := mul_le_mul_of_nonneg_left hnum (by positivity : (0:ℝ) ≤ η * (6:ℝ))
        linarith [hb2, hTx, hnum']
    · -- 7 ≤ L
      have hL7nat : 7 ≤ L := by omega
      have hL7 : (7:ℝ) ≤ (L:ℝ) := by exact_mod_cast hL7nat
      have hlogL7 : Real.log 7 ≤ Real.log (L:ℝ) := Real.log_le_log (by norm_num) hL7
      have hlogb : Real.log (1 + 10 * ((L:ℝ) - 1) / 3) ≤ 2 * Real.log 2 + Real.log (L:ℝ) := by
        rw [show (1:ℝ) + 10 * ((L:ℝ) - 1) / 3 = (10 * (L:ℝ) - 7) / 3 by ring]
        have h1 : Real.log ((10 * (L:ℝ) - 7) / 3) ≤ Real.log (4 * (L:ℝ)) := by
          apply Real.log_le_log
          · exact div_pos (by linarith) (by norm_num)
          · calc (10 * (L:ℝ) - 7) / 3 ≤ (12 * (L:ℝ)) / 3 :=
                  div_le_div_of_nonneg_right (by linarith) (by norm_num)
              _ = 4 * (L:ℝ) := by ring
        have h2 : Real.log (4 * (L:ℝ)) = 2 * Real.log 2 + Real.log (L:ℝ) := by
          rw [Real.log_mul (by norm_num : (4:ℝ) ≠ 0) (ne_of_gt hLpos), hlog4]
        linarith [h1, h2]
      have hTx := hT.trans (mul_le_mul_of_nonneg_left hlogb (by positivity))
      have hnum : 4 * Real.pi * (1 + Real.log (L:ℝ)) + 2 * Real.pi * (2 * Real.log 2 + Real.log (L:ℝ))
          + Real.pi ≤ 32 * Real.log (L:ℝ) := by
        nlinarith [hπ0, hπu, hπl, hd_l, hd_u, hlog7, hlogL7]
      have hnum' := mul_le_mul_of_nonneg_left hnum hxnn
      linarith [hb1, hTx, hnum']
  constructor
  · exact hmain1
  · have hmain1' : 2 * Real.pi * η * β + Real.log (1 + 20 * Real.pi * η * (L : ℝ) / 3) * m
        ≤ 32 * (η * (L : ℝ)) * Real.log (L : ℝ) - Real.pi * (η * (L:ℝ)) := by linarith [hmain1]
    have hsumlog : Real.log (L:ℝ) + Real.log (2 * (L:ℝ) / Real.pi) = Real.log (2 * (L:ℝ)^2 / Real.pi) := by
      rw [← Real.log_mul (ne_of_gt hLpos) (by positivity : (2 * (L:ℝ) / Real.pi) ≠ 0)]
      congr 1
      ring_nf
    linarith [hmain1', hh, hsumlog]

end Work.TMC16Core.Core
