import Mathlib
import Submission.Work.Recursion.defs

namespace Work.Recursion

open HvdH

/-- Monotonicity of a product of four nonnegative factors. -/
lemma mul_four_le_mul_four {a b c d a' b' c' d' : ℝ}
    (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') (hd : d ≤ d')
    (_ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) (hd0 : 0 ≤ d)
    (ha'0 : 0 ≤ a') (hb'0 : 0 ≤ b') (hc'0 : 0 ≤ c') :
    a * b * c * d ≤ a' * b' * c' * d' := by
  have h1 : a * b ≤ a' * b' := mul_le_mul ha hb hb0 ha'0
  have h2 : a * b * c ≤ a' * b' * c' := mul_le_mul h1 hc hc0 (mul_nonneg ha'0 hb'0)
  exact mul_le_mul h2 hd hd0 (mul_nonneg (mul_nonneg ha'0 hb'0) hc'0)

/-- The resampling term of `mainCost` (after cancelling `C`) is at most `(1/(8d)) n log₂ n`. -/
theorem est2 (K n : ℕ) (h : Work.Recursion.Est2Hyp K n) : Work.Recursion.Est2 K n := by
  obtain ⟨hK, hb, hT, hq, hα, hS, hSn, hbig⟩ := h
  have hrD : (0:ℝ) < rD := by norm_num [rD, HvdH.D]
  have hrD0 : (0:ℝ) ≤ 1/(8*rD) := by
    rw [one_div]; exact inv_nonneg.mpr (by linarith [hrD])
  have hb0 : (0:ℝ) < rB n := lt_of_lt_of_le zero_lt_one hb
  have hb0le : (0:ℝ) ≤ rB n := le_of_lt hb0
  have hnn : (0:ℝ) ≤ (n:ℝ) := by positivity
  have hK0 : (0:ℝ) ≤ (K:ℝ) := by positivity
  have hK1 : (1:ℝ) ≤ (K:ℝ) := by exact_mod_cast hK
  have hb1 : (1:ℝ) ≤ rB n := hb
  -- `T * b < 8n` gives `T ≤ 8n/b`
  have hTle : rT n ≤ 8 * (n:ℝ) / rB n := le_of_lt ((lt_div_iff₀ hb0).mpr hT)
  have hCpos : (0:ℝ) < (12 * rD ^ 2) ^ ((1:ℝ)/4) + 1 := by
    have h1 : (0:ℝ) ≤ 12 * rD^2 := mul_nonneg (by norm_num) (sq_nonneg rD)
    linarith [Real.rpow_nonneg h1 ((1:ℝ)/4)]
  set C := (12 * rD ^ 2) ^ ((1:ℝ)/4) + 1 with hC
  set L := Real.logb 2 (6 * (K:ℝ) * rB n) with hL
  have hC0 : (0:ℝ) ≤ C := le_of_lt hCpos
  have hdiv0 : (0:ℝ) ≤ 8 * (n:ℝ) / rB n := div_nonneg (by positivity) hb0le
  have hsqrt0 : (0:ℝ) ≤ 4 * Real.sqrt (rB n) := by positivity
  have hT0 : (0:ℝ) ≤ rT n := by simp only [rT]; positivity
  have hq0 : (0:ℝ) ≤ rQ (ppar n) + 1 := by simp only [rQ]; positivity
  have hα0 : (0:ℝ) ≤ rA n := by simp only [rA]; positivity
  -- `b ^ (3/4) = (1/b) * √b * b ^ (1/4) * b`
  have hpow : (1/rB n) * Real.sqrt (rB n) * rB n ^ ((1:ℝ)/4) * rB n = rB n ^ ((3:ℝ)/4) := by
    rw [Real.sqrt_eq_rpow]
    field_simp
    rw [← Real.rpow_add hb0]
    norm_num
  -- the product of the four upper bounds equals `192 * C * K² * b^{3/4} * (L+2) * n`
  have hid : (K:ℝ) * (8 * (n:ℝ) / rB n) * (4 * Real.sqrt (rB n)) * (C * rB n ^ ((1:ℝ)/4))
        * (6 * (K:ℝ) * rB n * (L + 2))
      = 192 * C * (K:ℝ)^2 * (rB n)^((3:ℝ)/4) * (L+2) * (n:ℝ) := by
    rw [← hpow]
    ring
  have hP : rP n = 6 * rB n := by simp [rP, rB, HvdH.ppar, Nat.cast_mul]
  have h6b : (1:ℝ) ≤ 6 * rB n := by linarith
  have hKp : 1 ≤ (K:ℝ) * (6 * rB n) := by
    have := mul_le_mul hK1 h6b (by norm_num : (0:ℝ) ≤ 1) hK0
    simpa using this
  have hKp0 : 0 ≤ (K:ℝ) * (6 * rB n) := le_trans zero_le_one hKp
  have hSbound : (K:ℝ) * rP n * rS (K * ppar n) + 1 ≤ 6 * (K:ℝ) * rB n * (L + 2) := by
    rw [hL, hP]
    have hS' : rS (K * ppar n) ≤ Real.logb 2 ((K:ℝ) * (6 * rB n)) + 1 := by simpa [hP] using hS
    have h3 : Real.logb 2 ((K:ℝ) * (6 * rB n)) = Real.logb 2 (6 * (K:ℝ) * rB n) := by ring_nf
    calc (K:ℝ) * (6 * rB n) * rS (K * ppar n) + 1
        ≤ (K:ℝ) * (6 * rB n) * (Real.logb 2 ((K:ℝ) * (6 * rB n)) + 1) + 1 :=
          add_le_add_left (mul_le_mul_of_nonneg_left hS' hKp0) 1
      _ ≤ 6 * (K:ℝ) * rB n * (Real.logb 2 (6 * (K:ℝ) * rB n) + 2) := by
          rw [h3]
          have hA : (K:ℝ) * (6 * rB n) * (Real.logb 2 (6 * (K:ℝ) * rB n) + 1) + 1
              ≤ (K:ℝ) * (6 * rB n) * (Real.logb 2 (6 * (K:ℝ) * rB n) + 1)
                + (K:ℝ) * (6 * rB n) := by linarith
          have hB : (K:ℝ) * (6 * rB n) * (Real.logb 2 (6 * (K:ℝ) * rB n) + 1)
                + (K:ℝ) * (6 * rB n)
              = (K:ℝ) * (6 * rB n) * (Real.logb 2 (6 * (K:ℝ) * rB n) + 2) := by ring
          have hD : (K:ℝ) * (6 * rB n) * (Real.logb 2 (6 * (K:ℝ) * rB n) + 2)
              = 6 * (K:ℝ) * rB n * (Real.logb 2 (6 * (K:ℝ) * rB n) + 2) := by ring
          linarith
  have hstep1 : (K:ℝ) * rT n * (rQ (ppar n) + 1) * rA n
      ≤ (K:ℝ) * (8 * (n:ℝ) / rB n) * (4 * Real.sqrt (rB n)) * (C * rB n ^ ((1:ℝ)/4)) := by
    exact mul_four_le_mul_four le_rfl hTle hq hα hK0 hT0 hq0 hα0 hK0 hdiv0 hsqrt0
  have hX0 : (0:ℝ) ≤ ((K:ℝ) * rP n) * rS (K * ppar n) + 1 := by
    have h1 : (0:ℝ) ≤ (K:ℝ) * rP n := mul_nonneg hK0 (by simp only [rP]; positivity)
    have h2 : (0:ℝ) ≤ rS (K * ppar n) := by simp only [rS]; positivity
    exact add_nonneg (mul_nonneg h1 h2) zero_le_one
  have hB0 : (0:ℝ) ≤ (K:ℝ) * (8 * (n:ℝ) / rB n) * (4 * Real.sqrt (rB n))
      * (C * rB n ^ ((1:ℝ)/4)) :=
    mul_nonneg (mul_nonneg (mul_nonneg hK0 hdiv0) hsqrt0)
      (mul_nonneg hC0 (Real.rpow_nonneg hb0le _))
  have hstep2 := mul_le_mul hstep1 hSbound hX0 hB0
  rw [hid] at hstep2
  have hbig' : 192 * C * (K:ℝ)^2 * (rB n)^((3:ℝ)/4) * (L+2)
      ≤ (1/(8*rD)) * Real.logb 2 (n:ℝ) := by
    simpa [hC, hL] using hbig
  have hstep3 : 192 * C * (K:ℝ)^2 * (rB n)^((3:ℝ)/4) * (L+2) * (n:ℝ)
      ≤ ((1/(8*rD)) * Real.logb 2 (n:ℝ)) * (n:ℝ) :=
    mul_le_mul_of_nonneg_right hbig' hnn
  have hstep4 : ((1/(8*rD)) * Real.logb 2 (n:ℝ)) * (n:ℝ) ≤ (1/(8*rD)) * ((n:ℝ) * rS n) := by
    have h1 : (1/(8*rD)) * Real.logb 2 (n:ℝ) * (n:ℝ) ≤ (1/(8*rD)) * rS n * (n:ℝ) := by
      apply mul_le_mul_of_nonneg_right _ hnn
      apply mul_le_mul_of_nonneg_left hSn hrD0
    calc ((1/(8*rD)) * Real.logb 2 (n:ℝ)) * (n:ℝ)
        = (1/(8*rD)) * Real.logb 2 (n:ℝ) * (n:ℝ) := rfl
      _ ≤ (1/(8*rD)) * rS n * (n:ℝ) := h1
      _ = (1/(8*rD)) * ((n:ℝ) * rS n) := by ring
  exact hstep2.trans (hstep3.trans hstep4)

end Work.Recursion
