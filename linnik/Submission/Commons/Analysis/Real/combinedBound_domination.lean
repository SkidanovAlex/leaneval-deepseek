import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.NormNum.RealSqrt

open Real
open scoped Real
set_option maxHeartbeats 4000000

namespace CBDev

-- ===== basic facts (from cb1) =====
lemma x_pos {x : ℝ} (hx : Real.exp 16 ≤ x) : 0 < x := lt_of_lt_of_le (Real.exp_pos 16) hx
lemma x_nonneg {x : ℝ} (hx : Real.exp 16 ≤ x) : 0 ≤ x := le_of_lt (x_pos hx)
lemma log_ge_16 {x : ℝ} (hx : Real.exp 16 ≤ x) : (16 : ℝ) ≤ Real.log x := by
  have h := Real.log_le_log (Real.exp_pos 16) hx
  simpa [Real.log_exp] using h
lemma log_pos {x : ℝ} (hx : Real.exp 16 ≤ x) : 0 < Real.log x := by linarith only [log_ge_16 hx]
lemma log_ge_one {x : ℝ} (hx : Real.exp 16 ≤ x) : (1 : ℝ) ≤ Real.log x := by linarith only [log_ge_16 hx]
lemma log_nonneg {x : ℝ} (hx : Real.exp 16 ≤ x) : 0 ≤ Real.log x := le_of_lt (log_pos hx)
lemma sqrt_pos {x : ℝ} (hx : Real.exp 16 ≤ x) : 0 < Real.sqrt x := Real.sqrt_pos.2 (x_pos hx)
lemma sqrt_ge_three {x : ℝ} (hx : Real.exp 16 ≤ x) : (3 : ℝ) ≤ Real.sqrt x := by
  have h32 : (32 : ℝ) ≤ Real.exp 16 := by
    have h := Real.two_mul_le_exp (x := (16 : ℝ))
    norm_num at h
    exact h
  have hx9 : (9 : ℝ) ≤ x := by linarith
  have hs := Real.sqrt_le_sqrt hx9
  norm_num [Real.sqrt_sq_eq_abs] at hs
  exact hs
lemma sqrt_ge_one {x : ℝ} (hx : Real.exp 16 ≤ x) : (1 : ℝ) ≤ Real.sqrt x := by linarith only [sqrt_ge_three hx]
lemma sqrt_nonneg {x : ℝ} (hx : Real.exp 16 ≤ x) : 0 ≤ Real.sqrt x := le_of_lt (sqrt_pos hx)

lemma cube_one_add_log_le {x : ℝ} (hx : Real.exp 16 ≤ x) :
    (1 + Real.log x) ^ 3 ≤ 8 * (Real.log x) ^ 3 := by
  have hsum : 1 + Real.log x ≤ 2 * Real.log x := by linarith only [log_ge_one hx]
  have hcube : (1 + Real.log x) ^ 3 ≤ (2 * Real.log x) ^ 3 :=
    pow_le_pow_left₀ (by linarith only [log_nonneg hx] : 0 ≤ 1 + Real.log x) hsum 3
  linarith only [hcube]

lemma L1_le_one_add_log {x : ℝ} (hx : Real.exp 16 ≤ x) :
    Real.log (Real.sqrt x + 3) + 1 ≤ 1 + Real.log x := by
  have hs0 : 0 ≤ Real.sqrt x := sqrt_nonneg hx
  have hpos : 0 < Real.sqrt x + 3 := by linarith
  have h2s_le : 2 * Real.sqrt x ≤ Real.sqrt x * Real.sqrt x := by
    exact mul_le_mul_of_nonneg_right (by linarith only [sqrt_ge_three hx] : (2 : ℝ) ≤ Real.sqrt x) hs0
  have hs3_le : Real.sqrt x + 3 ≤ x := by
    calc
      Real.sqrt x + 3 ≤ 2 * Real.sqrt x := by linarith only [sqrt_ge_three hx]
      _ ≤ Real.sqrt x * Real.sqrt x := h2s_le
      _ = x := Real.mul_self_sqrt (x_nonneg hx)
  have hlog := Real.log_le_log hpos hs3_le
  linarith

lemma L1_nonneg {x : ℝ} (hx : Real.exp 16 ≤ x) :
    0 ≤ Real.log (Real.sqrt x + 3) + 1 := by
  have h : 1 ≤ Real.sqrt x + 3 := by linarith only [sqrt_nonneg hx]
  have hlg : 0 ≤ Real.log (Real.sqrt x + 3) := Real.log_nonneg h
  linarith

lemma L2_le_one_add_log {x : ℝ} (hx : Real.exp 16 ≤ x) :
    Real.log (Real.sqrt x / (1 / 2 + 1 / Real.log x)) + 1 ≤ 1 + Real.log x := by
  let d : ℝ := 1 / 2 + 1 / Real.log x
  have htpos : 0 < Real.log x := log_pos hx
  have hd_pos : 0 < d := by dsimp [d]; positivity
  have hd_ge : (1 / 2 : ℝ) ≤ d := by
    dsimp [d]
    have h : 0 < 1 / Real.log x := one_div_pos.mpr htpos
    linarith
  have hs0 : 0 ≤ Real.sqrt x := sqrt_nonneg hx
  have h2s_le : 2 * Real.sqrt x ≤ Real.sqrt x * Real.sqrt x := by
    exact mul_le_mul_of_nonneg_right (by linarith only [sqrt_ge_three hx] : (2 : ℝ) ≤ Real.sqrt x) hs0
  have h1m : 1 ≤ 2 * d := by
    have hm := mul_le_mul_of_nonneg_left hd_ge (by norm_num : (0 : ℝ) ≤ 2)
    norm_num at hm
    simpa [mul_comm, mul_assoc] using hm
  have hs_le : Real.sqrt x ≤ 2 * Real.sqrt x * d := by
    have hm := mul_le_mul_of_nonneg_right h1m hs0
    simpa [mul_assoc, mul_comm, mul_left_comm] using hm
  have hdiv : Real.sqrt x / d ≤ 2 * Real.sqrt x := by
    rw [div_le_iff₀ hd_pos]
    simpa [mul_assoc, mul_comm, mul_left_comm] using hs_le
  have h2s_le_x : 2 * Real.sqrt x ≤ x := by
    calc
      2 * Real.sqrt x ≤ Real.sqrt x * Real.sqrt x := h2s_le
      _ = x := Real.mul_self_sqrt (x_nonneg hx)
  have hpos1 : 0 < Real.sqrt x / d := div_pos (sqrt_pos hx) hd_pos
  have hpos2 : 0 < 2 * Real.sqrt x := by exact mul_pos (by norm_num) (sqrt_pos hx)
  have hlog1 : Real.log (Real.sqrt x / d) ≤ Real.log (2 * Real.sqrt x) :=
    Real.log_le_log hpos1 hdiv
  have hlog2 : Real.log (2 * Real.sqrt x) ≤ Real.log x := Real.log_le_log hpos2 h2s_le_x
  have h : Real.log (Real.sqrt x / d) ≤ Real.log x := le_trans hlog1 hlog2
  linarith

lemma L2_nonneg {x : ℝ} (hx : Real.exp 16 ≤ x) :
    0 ≤ Real.log (Real.sqrt x / (1 / 2 + 1 / Real.log x)) + 1 := by
  have h1 : 1 ≤ Real.sqrt x / (1 / 2 + 1 / Real.log x) := by
    let d : ℝ := 1 / 2 + 1 / Real.log x
    have hd_le : d ≤ 1 := by
      dsimp [d]
      have h : 1 / Real.log x ≤ 1 / 2 := by
        exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) (by linarith only [log_ge_16 hx] : (2 : ℝ) ≤ Real.log x)
      linarith
    have hsge : 1 ≤ Real.sqrt x := sqrt_ge_one hx
    have htp : 0 < Real.log x := log_pos hx
    have hd_pos : 0 < d := by dsimp [d]; positivity
    have hdx : d ≤ Real.sqrt x := le_trans hd_le hsge
    have : 1 ≤ Real.sqrt x / d := by
      rw [le_div_iff₀ hd_pos]
      simpa using hdx
    simpa [d] using this
  have hlg : 0 ≤ Real.log (Real.sqrt x / (1 / 2 + 1 / Real.log x)) := Real.log_nonneg h1
  linarith

-- ===== perron equalities =====
lemma perron {x : ℝ} (hx : Real.exp 16 ≤ x) :
    x ^ (1 + 1 / Real.log x) = Real.exp 1 * x ∧
      x ^ (1 / 2 + 1 / Real.log x) = Real.exp 1 * Real.sqrt x := by
  have hxpos : 0 < x := x_pos hx
  have hlogpos : 0 < Real.log x := log_pos hx
  have hlogne : Real.log x ≠ 0 := ne_of_gt hlogpos
  have h1eq : x ^ (1 + 1 / Real.log x) = Real.exp 1 * x := by
    rw [Real.rpow_def_of_pos hxpos]
    have harg : Real.log x * (1 + 1 / Real.log x) = Real.log x + 1 := by
      field_simp [hlogne]
    rw [harg, Real.exp_add, Real.exp_log hxpos]
    ring
  have hsqrt : Real.exp (Real.log x / 2) = Real.sqrt x := by
    calc Real.exp (Real.log x / 2) = Real.exp (Real.log (Real.sqrt x)) := by
          rw [Real.log_sqrt (x_nonneg hx)]
        _ = Real.sqrt x := Real.exp_log (sqrt_pos hx)
  have h2eq : x ^ (1 / 2 + 1 / Real.log x) = Real.exp 1 * Real.sqrt x := by
    rw [Real.rpow_def_of_pos hxpos]
    have harg2 : Real.log x * (1 / 2 + 1 / Real.log x) = Real.log x / 2 + 1 := by
      field_simp [hlogne]
    rw [harg2, Real.exp_add, hsqrt]
    ring
  exact ⟨h1eq, h2eq⟩

-- ===== L1 cube, L2 three-log, product bound (all in x) =====

lemma L1_cube_le {x : ℝ} (hx : Real.exp 16 ≤ x) :
    (Real.log (Real.sqrt x + 3) + 1) ^ 3 ≤ 8 * (Real.log x) ^ 3 := by
  have h := pow_le_pow_left₀ (L1_nonneg hx) (L1_le_one_add_log hx) 3
  exact le_trans h (cube_one_add_log_le hx)

lemma L2_le_three_log {x : ℝ} (hx : Real.exp 16 ≤ x) :
    Real.log (Real.sqrt x / (1 / 2 + 1 / Real.log x)) + 1 ≤ 3 * Real.log x := by
  have h := L2_le_one_add_log hx
  linarith [log_ge_one hx]

-- (1+t)^3·(L1^3+8L2) ≤ 256 t^6, in s,t-free "x" statement form used inside:
lemma prod_bound (s t : ℝ) (ht1 : 1 ≤ t)
    (hL1c : (Real.log (s + 3) + 1) ^ 3 ≤ 8 * t ^ 3)
    (hL1n : 0 ≤ Real.log (s + 3) + 1)
    (hL2le : Real.log (s / (1 / 2 + 1 / t)) + 1 ≤ 3 * t)
    (hL2n : 0 ≤ Real.log (s / (1 / 2 + 1 / t)) + 1) :
    (1 + t) ^ 3 * ((Real.log (s + 3) + 1) ^ 3 + 8 * (Real.log (s / (1 / 2 + 1 / t)) + 1)) ≤
      256 * t ^ 6 := by
  have h1t3 : (1 + t) ^ 3 ≤ 8 * t ^ 3 := by
    have hsum : 1 + t ≤ 2 * t := by linarith
    have hcube : (1 + t) ^ 3 ≤ (2 * t) ^ 3 :=
      pow_le_pow_left₀ (by linarith : 0 ≤ 1 + t) hsum 3
    linarith only [hcube]
  have ht3 : t ≤ t ^ 3 := by
    have h := pow_le_pow_right₀ ht1 (by norm_num : (1 : ℕ) ≤ 3)
    simpa using h
  have h8L2 : 8 * (Real.log (s / (1 / 2 + 1 / t)) + 1) ≤ 24 * t ^ 3 := by
    have h1 : 8 * (Real.log (s / (1 / 2 + 1 / t)) + 1) ≤ 24 * t := by
      have hm := mul_le_mul_of_nonneg_left hL2le (by norm_num : (0 : ℝ) ≤ 8)
      linarith only [hm]
    have h2 : 24 * t ≤ 24 * t ^ 3 := by
      exact mul_le_mul_of_nonneg_left ht3 (by norm_num)
    exact le_trans h1 h2
  have hsum : (Real.log (s + 3) + 1) ^ 3 + 8 * (Real.log (s / (1 / 2 + 1 / t)) + 1) ≤ 32 * t ^ 3 := by
    have h8L2' : 8 * (Real.log (s / (1 / 2 + 1 / t)) + 1) ≤ 24 * t ^ 3 := h8L2
    linarith only [hL1c, h8L2']
  have hBn : 0 ≤ (Real.log (s + 3) + 1) ^ 3 + 8 * (Real.log (s / (1 / 2 + 1 / t)) + 1) := by
    have h1 : 0 ≤ (Real.log (s + 3) + 1) ^ 3 := pow_nonneg hL1n 3
    have h2 : 0 ≤ 8 * (Real.log (s / (1 / 2 + 1 / t)) + 1) := mul_nonneg (by norm_num) hL2n
    linarith
  have hb8n : 0 ≤ 8 * t ^ 3 := by
    have ht0 : 0 ≤ t := by linarith
    exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) (pow_nonneg ht0 3)
  have hmul := mul_le_mul h1t3 hsum hBn hb8n
  linarith only [hmul]

end CBDev

namespace CBDev

-- unit C coefficient bound, abstract (s,t) form
lemma cb_unit_aux {x s t : ℝ} (hx : Real.exp 16 ≤ x) (hs : s = Real.sqrt x)
    (ht : t = Real.log x) :
    (1 / (2 * Real.pi)) *
        (2 * ((1 + t) ^ 3 * (Real.log (s + 3) + 1) ^ 3 * x ^ (1 + 1 / t) * (1 / 2) / s) +
          8 * (1 + t) ^ 3 * x ^ (1 / 2 + 1 / t) * (Real.log (s / (1 / 2 + 1 / t)) + 1)) ≤
      1000000 * s * t ^ 10 := by
  have hsp : 0 < s := by rw [hs]; exact sqrt_pos hx
  have hs0 : 0 ≤ s := le_of_lt hsp
  have htp : 0 < t := by rw [ht]; exact log_pos hx
  have ht0 : 0 ≤ t := le_of_lt htp
  have ht1 : 1 ≤ t := by rw [ht]; exact log_ge_one hx
  have hper := perron hx
  have h1e : x ^ (1 + 1 / t) = Real.exp 1 * x := by simpa [ht] using hper.1
  have h2e : x ^ (1 / 2 + 1 / t) = Real.exp 1 * s := by
    simpa [ht, hs] using hper.2
  have hL1le : Real.log (s + 3) + 1 ≤ 1 + t := by simpa [hs, ht] using L1_le_one_add_log hx
  have hL1n : 0 ≤ Real.log (s + 3) + 1 := by simpa [hs] using L1_nonneg hx
  have hL1c : (Real.log (s + 3) + 1) ^ 3 ≤ 8 * t ^ 3 := by simpa [hs, ht] using L1_cube_le hx
  have hL2le : Real.log (s / (1 / 2 + 1 / t)) + 1 ≤ 1 + t := by
    simpa [hs, ht] using L2_le_one_add_log hx
  have hL2n : 0 ≤ Real.log (s / (1 / 2 + 1 / t)) + 1 := by simpa [hs, ht] using L2_nonneg hx
  have hL2le3 : Real.log (s / (1 / 2 + 1 / t)) + 1 ≤ 3 * t := by
    have h := hL2le
    nlinarith [ht1]
  have hprod := prod_bound s t ht1 hL1c hL1n hL2le3 hL2n
  have hBig0 : 0 ≤ (Real.log (s + 3) + 1) ^ 3 + 8 * (Real.log (s / (1 / 2 + 1 / t)) + 1) := by
    have h1 : 0 ≤ (Real.log (s + 3) + 1) ^ 3 := pow_nonneg hL1n 3
    have h2 : 0 ≤ 8 * (Real.log (s / (1 / 2 + 1 / t)) + 1) := mul_nonneg (by norm_num) hL2n
    linarith
  have hAn : 0 ≤ (1 + t) ^ 3 := pow_nonneg (by linarith : 0 ≤ 1 + t) 3
  have hC0 : 0 ≤ Real.exp 1 * s * (1 + t) ^ 3 *
      ((Real.log (s + 3) + 1) ^ 3 + 8 * (Real.log (s / (1 / 2 + 1 / t)) + 1)) := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt (Real.exp_pos 1)) hs0) hAn) hBig0
  have hinner_eq :
      2 * ((1 + t) ^ 3 * (Real.log (s + 3) + 1) ^ 3 * x ^ (1 + 1 / t) * (1 / 2) / s) +
          8 * (1 + t) ^ 3 * x ^ (1 / 2 + 1 / t) * (Real.log (s / (1 / 2 + 1 / t)) + 1) =
        Real.exp 1 * s * (1 + t) ^ 3 *
          ((Real.log (s + 3) + 1) ^ 3 + 8 * (Real.log (s / (1 / 2 + 1 / t)) + 1)) := by
    rw [h1e, h2e]
    have hxss : x = s * s := by
      rw [hs]
      exact (Real.mul_self_sqrt (x_nonneg hx)).symm
    rw [hxss]
    field_simp [ne_of_gt hsp]
  have hpi0 : (0 : ℝ) < 2 * Real.pi := by positivity
  have hone : (1 / (2 * Real.pi)) ≤ 1 := by
    have hpi2 : (1 : ℝ) ≤ 2 * Real.pi := by
      have h := Real.pi_gt_three
      linarith
    exact (div_le_iff₀ hpi0).2 (by simpa using hpi2)
  calc
    (1 / (2 * Real.pi)) *
        (2 * ((1 + t) ^ 3 * (Real.log (s + 3) + 1) ^ 3 * x ^ (1 + 1 / t) * (1 / 2) / s) +
          8 * (1 + t) ^ 3 * x ^ (1 / 2 + 1 / t) * (Real.log (s / (1 / 2 + 1 / t)) + 1))
        = (1 / (2 * Real.pi)) * (Real.exp 1 * s * (1 + t) ^ 3 *
          ((Real.log (s + 3) + 1) ^ 3 + 8 * (Real.log (s / (1 / 2 + 1 / t)) + 1))) := by
          rw [hinner_eq]
    _ ≤ Real.exp 1 * s * (1 + t) ^ 3 *
          ((Real.log (s + 3) + 1) ^ 3 + 8 * (Real.log (s / (1 / 2 + 1 / t)) + 1)) := by
          simpa using (mul_le_mul_of_nonneg_right hone hC0)
    _ ≤ 3 * s * (8 * t ^ 3) * (32 * t ^ 3) := by
          have h1t3 : (1 + t) ^ 3 ≤ 8 * t ^ 3 := by
            have hsum : 1 + t ≤ 2 * t := by linarith
            have hcube : (1 + t) ^ 3 ≤ (2 * t) ^ 3 :=
              pow_le_pow_left₀ (by linarith : 0 ≤ 1 + t) hsum 3
            linarith only [hcube]
          have hL1p8 : (Real.log (s + 3) + 1) ^ 3 + 8 * (Real.log (s / (1 / 2 + 1 / t)) + 1) ≤ 32 * t ^ 3 := by
            have h8L2 : 8 * (Real.log (s / (1 / 2 + 1 / t)) + 1) ≤ 24 * t ^ 3 := by
              have h1 : 8 * (Real.log (s / (1 / 2 + 1 / t)) + 1) ≤ 24 * t := by
                have hm := mul_le_mul_of_nonneg_left hL2le3 (by norm_num : (0 : ℝ) ≤ 8)
                linarith only [hm]
              have ht3 : t ≤ t ^ 3 := by
                have h := pow_le_pow_right₀ ht1 (by norm_num : (1 : ℕ) ≤ 3)
                simpa using h
              have h2 : 24 * t ≤ 24 * t ^ 3 := mul_le_mul_of_nonneg_left ht3 (by norm_num)
              exact le_trans h1 h2
            linarith only [hL1c, h8L2]
          have hb8n : 0 ≤ 8 * t ^ 3 := mul_nonneg (by norm_num) (pow_nonneg ht0 3)
          have h1 : Real.exp 1 * s * (1 + t) ^ 3 *
              ((Real.log (s + 3) + 1) ^ 3 + 8 * (Real.log (s / (1 / 2 + 1 / t)) + 1)) ≤
              3 * s * (8 * t ^ 3) * (32 * t ^ 3) := by
            have h1' : s * (1 + t) ^ 3 *
                ((Real.log (s + 3) + 1) ^ 3 + 8 * (Real.log (s / (1 / 2 + 1 / t)) + 1)) ≤
                s * (8 * t ^ 3) * (32 * t ^ 3) := by
              have hA' : s * (1 + t) ^ 3 ≤ s * (8 * t ^ 3) :=
                mul_le_mul_of_nonneg_left h1t3 hs0
              exact mul_le_mul hA' hL1p8 hBig0 (mul_nonneg hs0 hb8n)
            have hn : 0 ≤ s * (1 + t) ^ 3 *
                ((Real.log (s + 3) + 1) ^ 3 + 8 * (Real.log (s / (1 / 2 + 1 / t)) + 1)) :=
              mul_nonneg (mul_nonneg hs0 hAn) hBig0
            calc
              Real.exp 1 * s * (1 + t) ^ 3 *
                  ((Real.log (s + 3) + 1) ^ 3 + 8 * (Real.log (s / (1 / 2 + 1 / t)) + 1))
                  = Real.exp 1 * (s * (1 + t) ^ 3 *
                    ((Real.log (s + 3) + 1) ^ 3 + 8 * (Real.log (s / (1 / 2 + 1 / t)) + 1))) := by
                    ring
              _ ≤ 3 * (s * (8 * t ^ 3) * (32 * t ^ 3)) := by
                    have he3 : Real.exp 1 ≤ 3 := le_of_lt Real.exp_one_lt_three
                    exact mul_le_mul he3 h1' hn (by norm_num : (0 : ℝ) ≤ 3)
              _ = 3 * s * (8 * t ^ 3) * (32 * t ^ 3) := by ring
          exact h1
    _ = 768 * s * t ^ 6 := by ring
    _ ≤ 1000000 * s * t ^ 10 := by
          have ht6 : t ^ 6 ≤ t ^ 10 := pow_le_pow_right₀ ht1 (by norm_num : (6 : ℕ) ≤ 10)
          have h1 : s * t ^ 6 ≤ s * t ^ 10 := mul_le_mul_of_nonneg_left ht6 hs0
          have h2 : 768 * (s * t ^ 6) ≤ 768 * (s * t ^ 10) :=
            mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 768)
          have hstn : 0 ≤ s * t ^ 10 := mul_nonneg hs0 (pow_nonneg ht0 10)
          have h3 : 768 * (s * t ^ 10) ≤ 1000000 * (s * t ^ 10) :=
            mul_le_mul_of_nonneg_right (by norm_num : (768 : ℝ) ≤ 1000000) hstn
          calc
            768 * s * t ^ 6 = 768 * (s * t ^ 6) := by ring
            _ ≤ 768 * (s * t ^ 10) := h2
            _ ≤ 1000000 * (s * t ^ 10) := h3
            _ = 1000000 * s * t ^ 10 := by ring

end CBDev

namespace CBDev

lemma cb_unit_le {x : ℝ} (hx : Real.exp 16 ≤ x) :
    (1 / (2 * Real.pi)) *
        (2 * ((1 + Real.log x) ^ 3 * (Real.log (Real.sqrt x + 3) + 1) ^ 3 *
            x ^ (1 + 1 / Real.log x) * (1 / 2) / Real.sqrt x) +
          8 * (1 + Real.log x) ^ 3 * x ^ (1 / 2 + 1 / Real.log x) *
            (Real.log (Real.sqrt x / (1 / 2 + 1 / Real.log x)) + 1)) ≤
      1000000 * Real.sqrt x * (Real.log x) ^ 10 := by
  exact cb_unit_aux hx rfl rfl

lemma cb_A_le_R0 {x : ℝ} (hx : Real.exp 16 ≤ x) :
    x * (Real.log x) ^ 2 / Real.sqrt x + Real.log x ≤
      1000000 * Real.sqrt x * (Real.log x) ^ 10 := by
  have hsp : 0 < Real.sqrt x := sqrt_pos hx
  have hs0 : 0 ≤ Real.sqrt x := le_of_lt hsp
  have ht0 : 0 ≤ Real.log x := log_nonneg hx
  have ht1 : 1 ≤ Real.log x := log_ge_one hx
  have hxss : x = Real.sqrt x * Real.sqrt x := (Real.mul_self_sqrt (x_nonneg hx)).symm
  have hpart1 : x * (Real.log x) ^ 2 / Real.sqrt x ≤ Real.sqrt x * (Real.log x) ^ 2 := by
    rw [div_le_iff₀ hsp]
    nth_rw 1 [hxss]
    exact le_of_eq (by ring)
  have hst1 : 1 ≤ Real.sqrt x * Real.log x := by
    simpa using (mul_le_mul (sqrt_ge_one hx) (log_ge_one hx) (by norm_num) (sqrt_nonneg hx))
  have hpart2 : Real.log x ≤ Real.sqrt x * (Real.log x) ^ 2 := by
    have hm := mul_le_mul_of_nonneg_right hst1 ht0
    simpa [mul_assoc, pow_two] using hm
  have htwo : x * (Real.log x) ^ 2 / Real.sqrt x + Real.log x ≤
      2 * Real.sqrt x * (Real.log x) ^ 2 := by
    have h := add_le_add hpart1 hpart2
    linarith
  calc
    x * (Real.log x) ^ 2 / Real.sqrt x + Real.log x ≤
        2 * Real.sqrt x * (Real.log x) ^ 2 := htwo
    _ = (2 * Real.sqrt x) * (Real.log x) ^ 2 := by ring
    _ ≤ (2 * Real.sqrt x) * (Real.log x) ^ 10 := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ ht1 (by norm_num : (2 : ℕ) ≤ 10)) (by linarith)
    _ = 2 * Real.sqrt x * (Real.log x) ^ 10 := by ring
    _ ≤ 1000000 * Real.sqrt x * (Real.log x) ^ 10 := by
      have hstn : 0 ≤ Real.sqrt x * (Real.log x) ^ 10 :=
        mul_nonneg hs0 (pow_nonneg ht0 10)
      have hm := mul_le_mul_of_nonneg_right (by norm_num : (2 : ℝ) ≤ 1000000) hstn
      simpa [mul_assoc, mul_comm, mul_left_comm] using hm

end CBDev

namespace Commons.Analysis.Real

theorem combinedBound_domination {C P x : ℝ} (hC : 0 < C) (hP : 0 ≤ P)
    (hx : Real.exp 16 ≤ x) :
    P * (x * (Real.log x) ^ 2 / Real.sqrt x + Real.log x) +
        (1 / (2 * Real.pi)) *
          (2 * (C * (1 + Real.log x) ^ 3 * (Real.log (Real.sqrt x + 3) + 1) ^ 3 *
              (x : ℝ) ^ (1 + 1 / Real.log x) * (1 / 2) / Real.sqrt x) +
           8 * C * (1 + Real.log x) ^ 3 * (x : ℝ) ^ (1 / 2 + 1 / Real.log x) *
             (Real.log (Real.sqrt x / (1 / 2 + 1 / Real.log x)) + 1)) ≤
      (P + C + 1) * 1000000 * Real.sqrt x * (Real.log x) ^ 10 := by
  have hA := CBDev.cb_A_le_R0 hx
  have hU := CBDev.cb_unit_le hx
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
            (Real.log (Real.sqrt x / (1 / 2 + 1 / Real.log x)) + 1))) ≤
      C * (1000000 * Real.sqrt x * (Real.log x) ^ 10) :=
    mul_le_mul_of_nonneg_left hU hC0
  calc
    P * (x * (Real.log x) ^ 2 / Real.sqrt x + Real.log x) +
        (1 / (2 * Real.pi)) *
          (2 * (C * (1 + Real.log x) ^ 3 * (Real.log (Real.sqrt x + 3) + 1) ^ 3 *
              (x : ℝ) ^ (1 + 1 / Real.log x) * (1 / 2) / Real.sqrt x) +
           8 * C * (1 + Real.log x) ^ 3 * (x : ℝ) ^ (1 / 2 + 1 / Real.log x) *
             (Real.log (Real.sqrt x / (1 / 2 + 1 / Real.log x)) + 1))
        = P * (x * (Real.log x) ^ 2 / Real.sqrt x + Real.log x) +
          C * ((1 / (2 * Real.pi)) *
            (2 * ((1 + Real.log x) ^ 3 * (Real.log (Real.sqrt x + 3) + 1) ^ 3 *
                x ^ (1 + 1 / Real.log x) * (1 / 2) / Real.sqrt x) +
              8 * (1 + Real.log x) ^ 3 * x ^ (1 / 2 + 1 / Real.log x) *
                (Real.log (Real.sqrt x / (1 / 2 + 1 / Real.log x)) + 1))) := by ring
    _ ≤ P * (1000000 * Real.sqrt x * (Real.log x) ^ 10) +
        C * (1000000 * Real.sqrt x * (Real.log x) ^ 10) := add_le_add hA' hU'
    _ = (P + C) * (1000000 * Real.sqrt x * (Real.log x) ^ 10) := by ring
    _ ≤ (P + C + 1) * (1000000 * Real.sqrt x * (Real.log x) ^ 10) := by
      exact mul_le_mul_of_nonneg_right (by linarith) hR0
    _ = (P + C + 1) * 1000000 * Real.sqrt x * (Real.log x) ^ 10 := by ring

end Commons.Analysis.Real