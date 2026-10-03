import Mathlib
import Submission.Work.FIArea4.S15EGDefs
import Submission.Work.FIArea4.S15cutDefs

namespace Work.FIArea4

/-!
# `Work.FIArea4.S15EG_crude_piece3`

The third (and crudest) factor of the §15 crude bound.  The two support bounds
`Re = S15EG_Re Pa e`, `Se = S15EG_Se Pa` of the stratum box satisfy the crude
estimates

`Re · Se ≤ 8 N`,  `2·Re·Se ≤ 16 N`,  `log (2·Re·Se) + 1 ≤ 4 (log N + 1)`,

so that, since `2 ≥ 1`,

`16 (Y/e)^{1/3} (Re·Se)^{2/3} (log (2·Re·Se) + 1)^4
   ≤ 16 · 4 · 256 · Y^{1/3} N^{2/3} (log N + 1)^4
   = 16384 Y^{1/3} N^{2/3} (log N + 1)^4
   ≤ 30000 Y^{1/3} N^{2/3} (log N + 1)^4`.

The point of the constant `30000` is only that it dominates `16 · 4 · 256 = 16384`.
-/

/-- `(8 : ℝ) ^ (2/3) = 4`. -/
lemma S15EG_crude_eight_rpow : (8 : ℝ) ^ ((2 : ℝ) / 3) = 4 := by
  have h8 : (8 : ℝ) = (2 : ℝ) ^ ((3 : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]; norm_num
  rw [h8, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) ((3 : ℕ) : ℝ) ((2 : ℝ) / 3)]
  have he : ((3 : ℕ) : ℝ) * ((2 : ℝ) / 3) = 2 := by norm_num
  rw [he, Real.rpow_two]
  norm_num

/-- The product of the two support bounds of the stratum box is at most `8N`. -/
lemma S15EG_crude_RS_le (Pa : Work.FITop.Params) (e : ℕ) (he : 1 ≤ e) :
    (S15EG_Re Pa e : ℝ) * (S15EG_Se Pa : ℝ) ≤ 8 * Pa.N := by
  have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
  have hdiv : S15EG_K Pa / (2 * e) ≤ S15EG_K Pa / 2 :=
    Nat.div_le_div_left (by omega : 2 ≤ 2 * e) (by norm_num)
  have hRcast : (S15EG_Re Pa e : ℝ) = ((S15EG_K Pa / (2 * e) : ℕ) : ℝ) + 1 := by
    rw [S15EG_Re]; push_cast; ring
  have hScast : (S15EG_Se Pa : ℝ) = ((S15EG_K Pa / 2 : ℕ) : ℝ) + 1 := by
    rw [S15EG_Se]; push_cast; ring
  have hdivK : ((S15EG_K Pa / 2 : ℕ) : ℝ) ≤ (S15EG_K Pa : ℝ) / 2 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    exact_mod_cast Nat.div_mul_le_self (S15EG_K Pa) 2
  have hRS : (S15EG_Re Pa e : ℝ) ≤ (S15EG_Se Pa : ℝ) := by
    rw [hRcast, hScast]
    have h1 : ((S15EG_K Pa / (2 * e) : ℕ) : ℝ) ≤ ((S15EG_K Pa / 2 : ℕ) : ℝ) := by
      exact_mod_cast hdiv
    linarith
  have hS2 : (S15EG_Se Pa : ℝ) ≤ (3 : ℝ) / 2 * Real.sqrt Pa.N + 1 := by
    rw [hScast]
    have hK := S15EG_K_le Pa
    linarith
  have hR0 : (0 : ℝ) ≤ (S15EG_Re Pa e : ℝ) := Nat.cast_nonneg _
  have hS0 : (0 : ℝ) ≤ (S15EG_Se Pa : ℝ) := Nat.cast_nonneg _
  have hsq : (S15EG_Se Pa : ℝ) ^ 2 ≤ ((3 : ℝ) / 2 * Real.sqrt Pa.N + 1) ^ 2 :=
    pow_le_pow_left₀ hS0 hS2 2
  have hsqrt0 : (0 : ℝ) ≤ Real.sqrt Pa.N := Real.sqrt_nonneg _
  have hsqN : Real.sqrt Pa.N ^ 2 = Pa.N := Real.sq_sqrt (by linarith)
  have hle : Real.sqrt Pa.N ≤ Pa.N := by
    have h1 : Real.sqrt Pa.N ≤ Real.sqrt (Pa.N ^ 2) := by
      apply Real.sqrt_le_sqrt
      nlinarith
    rwa [Real.sqrt_sq (by linarith)] at h1
  have hfin : ((3 : ℝ) / 2 * Real.sqrt Pa.N + 1) ^ 2 ≤ 8 * Pa.N := by
    nlinarith [hsqN, hsqrt0, hle, hN1]
  calc (S15EG_Re Pa e : ℝ) * (S15EG_Se Pa : ℝ)
      ≤ (S15EG_Se Pa : ℝ) * (S15EG_Se Pa : ℝ) := mul_le_mul_of_nonneg_right hRS hS0
    _ = (S15EG_Se Pa : ℝ) ^ 2 := by ring
    _ ≤ ((3 : ℝ) / 2 * Real.sqrt Pa.N + 1) ^ 2 := hsq
    _ ≤ 8 * Pa.N := hfin

/-- Comparison of the fourth powers of the two logarithmic factors: if `T ≥ 1` and
`2T ≤ 16N` with `N ≥ 1`, then `(log (2T) + 1)^4 ≤ 256 (log N + 1)^4`. -/
lemma S15EG_crude_log_quad_le (N T : ℝ) (hN : 1 ≤ N) (hT : 1 ≤ T) (hT2 : 2 * T ≤ 16 * N) :
    (Real.log (2 * T) + 1) ^ (4 : ℕ) ≤ 256 * (Real.log N + 1) ^ (4 : ℕ) := by
  have hlog16 : Real.log (16 : ℝ) < 3 := by
    have h : Real.log (16 : ℝ) = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
      norm_num
    rw [h]; linarith [Real.log_two_lt_d9]
  have hlogN : (0 : ℝ) ≤ Real.log N := Real.log_nonneg hN
  have h2T : (0 : ℝ) < 2 * T := by linarith
  have h1 : Real.log (2 * T) ≤ Real.log (16 * N) := Real.log_le_log h2T hT2
  have h2 : Real.log (16 * N) = Real.log 16 + Real.log N := by
    rw [Real.log_mul (by norm_num) (by linarith)]
  have h3 : Real.log (2 * T) + 1 ≤ 4 * (Real.log N + 1) := by linarith
  have h4 : (0 : ℝ) ≤ Real.log (2 * T) + 1 := by
    have : (0 : ℝ) ≤ Real.log (2 * T) := Real.log_nonneg (by linarith)
    linarith
  calc (Real.log (2 * T) + 1) ^ (4 : ℕ)
      ≤ (4 * (Real.log N + 1)) ^ (4 : ℕ) := pow_le_pow_left₀ h4 h3 4
    _ = 256 * (Real.log N + 1) ^ (4 : ℕ) := by rw [mul_pow]; norm_num

/-- The abstract real-analytic core of `S15EG_crude_piece3`. -/
lemma S15EG_crude_aux (e : ℕ) (Y R S N : ℝ) (he : 1 ≤ e)
    (hY1 : 1 ≤ Y) (hN1 : 1 ≤ N) (hR1 : 1 ≤ R) (hS1 : 1 ≤ S)
    (hRS : R * S ≤ 8 * N) :
    16 * (Y / (e : ℝ)) ^ ((1 : ℝ) / 3) * (R * S) ^ ((2 : ℝ) / 3)
        * (Real.log (2 * R * S) + 1) ^ (4 : ℕ)
      ≤ 30000 * Y ^ ((1 : ℝ) / 3) * N ^ ((2 : ℝ) / 3) * (Real.log N + 1) ^ (4 : ℕ) := by
  have hY0 : (0 : ℝ) ≤ Y := by linarith
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have he0 : (0 : ℝ) < (e : ℝ) := by
    have : (1 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
    linarith
  have he1 : (1 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
  have hRS0 : (0 : ℝ) ≤ R * S := mul_nonneg (by linarith) (by linarith)
  have hRS1 : (1 : ℝ) ≤ R * S := by
    have h := mul_le_mul hR1 hS1 (show (0 : ℝ) ≤ 1 by norm_num) (by linarith)
    simpa using h
  have hRS2 : (2 : ℝ) * (R * S) ≤ 16 * N := by linarith
  have hYp : (0 : ℝ) ≤ Y ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hY0 _
  have hNp : (0 : ℝ) ≤ N ^ ((2 : ℝ) / 3) := Real.rpow_nonneg hN0 _
  have hRSp : (0 : ℝ) ≤ (R * S) ^ ((2 : ℝ) / 3) := Real.rpow_nonneg hRS0 _
  -- (1) the `Y`-factor
  have hYe : Y / (e : ℝ) ≤ Y := by
    rw [div_le_iff₀ he0]
    have h1 : Y * 1 ≤ Y * (e : ℝ) := mul_le_mul_of_nonneg_left he1 hY0
    simpa using h1
  have hA : (Y / (e : ℝ)) ^ ((1 : ℝ) / 3) ≤ Y ^ ((1 : ℝ) / 3) :=
    Real.rpow_le_rpow (div_nonneg hY0 (by linarith)) hYe (by norm_num)
  have hA' : 16 * (Y / (e : ℝ)) ^ ((1 : ℝ) / 3) ≤ 16 * Y ^ ((1 : ℝ) / 3) :=
    mul_le_mul_of_nonneg_left hA (by norm_num)
  -- (2) the `Re·Se`-factor
  have hB : (R * S) ^ ((2 : ℝ) / 3) ≤ 4 * N ^ ((2 : ℝ) / 3) := by
    have h1 : (R * S) ^ ((2 : ℝ) / 3) ≤ (8 * N) ^ ((2 : ℝ) / 3) :=
      Real.rpow_le_rpow hRS0 hRS (by norm_num)
    have h2 : (8 * N) ^ ((2 : ℝ) / 3) = 4 * N ^ ((2 : ℝ) / 3) := by
      rw [Real.mul_rpow (by norm_num) hN0, S15EG_crude_eight_rpow]
    rwa [h2] at h1
  -- (3) the logarithmic factor
  have hC : (Real.log (2 * R * S) + 1) ^ (4 : ℕ) ≤ 256 * (Real.log N + 1) ^ (4 : ℕ) := by
    have h := S15EG_crude_log_quad_le N (R * S) hN1 hRS1 hRS2
    rwa [show (2 : ℝ) * (R * S) = 2 * R * S from by ring] at h
  have hC' : (0 : ℝ) ≤ (Real.log (2 * R * S) + 1) ^ (4 : ℕ) := by
    apply pow_nonneg
    have harg : (2 : ℝ) * (R * S) = 2 * R * S := by ring
    have h2RS : (1 : ℝ) ≤ 2 * (R * S) := by linarith
    have h2RS' : (1 : ℝ) ≤ 2 * R * S := by rw [← harg]; exact h2RS
    linarith [Real.log_nonneg h2RS']
  -- assembly
  have h1 : 16 * (Y / (e : ℝ)) ^ ((1 : ℝ) / 3) * (R * S) ^ ((2 : ℝ) / 3)
      ≤ 16 * Y ^ ((1 : ℝ) / 3) * (4 * N ^ ((2 : ℝ) / 3)) :=
    mul_le_mul hA' hB hRSp (by linarith)
  have h2 : 16 * (Y / (e : ℝ)) ^ ((1 : ℝ) / 3) * (R * S) ^ ((2 : ℝ) / 3)
        * (Real.log (2 * R * S) + 1) ^ (4 : ℕ)
      ≤ 16 * Y ^ ((1 : ℝ) / 3) * (4 * N ^ ((2 : ℝ) / 3))
        * (256 * (Real.log N + 1) ^ (4 : ℕ)) :=
    mul_le_mul h1 hC hC' (mul_nonneg (by linarith) (by linarith))
  have hW : (0 : ℝ) ≤ Y ^ ((1 : ℝ) / 3) * N ^ ((2 : ℝ) / 3) * (Real.log N + 1) ^ (4 : ℕ) :=
    mul_nonneg (mul_nonneg hYp hNp)
      (pow_nonneg (by linarith [Real.log_nonneg hN1]) 4)
  calc 16 * (Y / (e : ℝ)) ^ ((1 : ℝ) / 3) * (R * S) ^ ((2 : ℝ) / 3)
        * (Real.log (2 * R * S) + 1) ^ (4 : ℕ)
      ≤ 16 * Y ^ ((1 : ℝ) / 3) * (4 * N ^ ((2 : ℝ) / 3))
        * (256 * (Real.log N + 1) ^ (4 : ℕ)) := h2
    _ = 16384 * (Y ^ ((1 : ℝ) / 3) * N ^ ((2 : ℝ) / 3) * (Real.log N + 1) ^ (4 : ℕ)) := by
        ring
    _ ≤ 30000 * (Y ^ ((1 : ℝ) / 3) * N ^ ((2 : ℝ) / 3) * (Real.log N + 1) ^ (4 : ℕ)) :=
        mul_le_mul_of_nonneg_right (by norm_num) hW
    _ = 30000 * Y ^ ((1 : ℝ) / 3) * N ^ ((2 : ℝ) / 3) * (Real.log N + 1) ^ (4 : ℕ) := by
        ring

set_option linter.unusedVariables false in
theorem S15EG_crude_piece3 (Pa : Work.FITop.Params) (X j e : ℕ) (hX : 1 ≤ X) (he : 1 ≤ e) :
    (16 : ℝ) * ((Work.FIArea4.S15Y Pa X j : ℝ) / (e : ℝ)) ^ ((1 : ℝ) / 3)
        * (((Work.FIArea4.S15EG_Re Pa e : ℝ) * (Work.FIArea4.S15EG_Se Pa : ℝ)) ^ ((2 : ℝ) / 3))
        * (Real.log (2 * (Work.FIArea4.S15EG_Re Pa e : ℝ) * (Work.FIArea4.S15EG_Se Pa : ℝ)) + 1) ^ (4 : ℕ)
      ≤ 30000 * ((Work.FIArea4.S15Y Pa X j : ℝ)) ^ ((1 : ℝ) / 3)
          * Pa.N ^ ((2 : ℝ) / 3) * (Real.log Pa.N + 1) ^ (4 : ℕ) := by
  have hYn : 1 ≤ S15Y Pa X j := by
    rw [S15Y]; exact Nat.le_add_left 1 _
  have hY1 : (1 : ℝ) ≤ (S15Y Pa X j : ℝ) := by exact_mod_cast hYn
  have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
  have hR1 : (1 : ℝ) ≤ (S15EG_Re Pa e : ℝ) := by exact_mod_cast S15EG_Re_pos Pa e
  have hS1 : (1 : ℝ) ≤ (S15EG_Se Pa : ℝ) := by exact_mod_cast S15EG_Se_pos Pa
  have hRS : (S15EG_Re Pa e : ℝ) * (S15EG_Se Pa : ℝ) ≤ 8 * Pa.N :=
    S15EG_crude_RS_le Pa e he
  exact S15EG_crude_aux e _ _ _ _ he hY1 hN1 hR1 hS1 hRS

end Work.FIArea4
