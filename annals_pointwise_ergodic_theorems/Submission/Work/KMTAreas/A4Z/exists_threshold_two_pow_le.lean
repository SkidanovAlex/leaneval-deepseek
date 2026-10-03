import Mathlib
import Submission.Work.KMTAreas.A4Z.Defs

set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A4Z

open Work.Analysis.EndVar

/-- `log₂ (C · 2^{l/4}) = log₂ C + l/4`. -/
private lemma logb_two_mul_rpow_quarter (C : ℝ) (hC : 0 < C) (l : ℕ) :
    Real.logb 2 (C * (2 : ℝ) ^ ((l : ℝ) / 4)) = Real.logb 2 C + (l : ℝ) / 4 := by
  rw [Real.logb_mul (ne_of_gt hC)
    (ne_of_gt (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) _))]
  rw [Real.logb_rpow (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) ≠ 1)]

/-- `Log N ≤ log₂ N` for `N ≥ 2`. -/
private lemma logN_le_logb_two {N : ℕ} (hN : 2 ≤ N) :
    (Work.Analysis.EndVar.logN N : ℝ) ≤ Real.logb 2 (N : ℝ) := by
  have hmax : max N 2 = N := max_eq_left hN
  have hlogNeq : Work.Analysis.EndVar.logN N = ((Nat.log 2 N : ℕ) : ℤ) := by
    simp only [Work.Analysis.EndVar.logN, hmax]
  rw [hlogNeq, Int.cast_natCast]
  have hN0 : N ≠ 0 := by omega
  have hpow : (2 : ℝ) ^ (Nat.log 2 N : ℕ) ≤ (N : ℝ) := by
    have h := Nat.pow_log_le_self 2 hN0
    have h' : (((2 : ℕ) ^ Nat.log 2 N : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast h
    simpa using h'
  have h0 : (0 : ℝ) < (2 : ℝ) ^ (Nat.log 2 N) := by positivity
  have h := Real.logb_le_logb_of_le (b := 2) (by norm_num : (1:ℝ) < 2) h0 hpow
  rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2), mul_one] at h

theorem exists_threshold_two_pow_le (C : ℝ) (hC : 0 < C) (d : ℕ) (hd : 2 ≤ d) :
    ∃ L₀ : ℕ, ∀ (l l' : ℕ) (k' : ℤ) (N : ℕ), L₀ ≤ l → 1 ≤ N →
      (2 : ℝ) ^ l' ≤ C * (2 : ℝ) ^ ((l : ℝ) / 4) →
      (2 : ℝ) ^ k' ≤ C * (2 : ℝ) ^ ((l : ℝ) / 4) / (N : ℝ) ^ d →
      l' ≤ l ∧ k' ≤ (d : ℤ) * ((l : ℤ) - Work.Analysis.EndVar.logN N) - 1 := by
  obtain ⟨L₀, hL₀⟩ := exists_nat_gt (4 * |Real.logb 2 C| + 4 * (d : ℝ) + 16)
  refine ⟨L₀, ?_⟩
  intro l l' k' N hl hN h1 h2
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hlR : 4 * |Real.logb 2 C| + 4 * (d : ℝ) + 16 ≤ (l : ℝ) := by
    have h : (L₀ : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
    linarith
  have hl0 : (0 : ℝ) ≤ (l : ℝ) := by positivity
  have habs : |Real.logb 2 C| ≤ (l : ℝ) / 4 := by linarith
  have hA_le : Real.logb 2 C ≤ (l : ℝ) / 4 := le_trans (le_abs_self _) habs
  have hgoal1 : Real.logb 2 C + (l : ℝ) / 4 ≤ (l : ℝ) := by linarith
  have hgoal2 : Real.logb 2 C + (l : ℝ) / 4 ≤ (d : ℝ) * (l : ℝ) - (d : ℝ) - 1 := by
    have hdl : (d : ℝ) ≤ (l : ℝ) / 4 := by
      linarith [abs_nonneg (Real.logb 2 C)]
    have h2' : (2 : ℝ) * (l : ℝ) ≤ (d : ℝ) * (l : ℝ) := by
      have h := mul_le_mul_of_nonneg_right hdR hl0
      linarith
    have h1' : Real.logb 2 C + (l : ℝ) / 4 ≤ (l : ℝ) / 2 := by linarith
    linarith
  -- Part 1: `l' ≤ l`
  have h1r : (2 : ℝ) ^ (l' : ℝ) ≤ C * (2 : ℝ) ^ ((l : ℝ) / 4) := by
    rw [Real.rpow_natCast]; exact h1
  have hl'_le : (l' : ℝ) ≤ (l : ℝ) := by
    have hmono := Real.logb_le_logb_of_le (b := 2) (by norm_num : (1:ℝ) < 2)
      (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) (l' : ℝ)) h1r
    rw [Real.logb_rpow (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) ≠ 1)] at hmono
    rw [logb_two_mul_rpow_quarter C hC l] at hmono
    linarith
  refine ⟨by exact_mod_cast hl'_le, ?_⟩
  -- Part 2: `k' ≤ d (l - Log N) - 1`
  have hkR : (k' : ℝ) ≤ (d : ℝ) * ((l : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) - 1 := by
    by_cases hN1 : N = 1
    · subst hN1
      have hlogN1 : (Work.Analysis.EndVar.logN 1 : ℝ) = 1 := by
        have h : Nat.log 2 (max 1 2) = 1 := by
          have := Nat.log_pow (b := 2) (by norm_num : 1 < 2) 1
          simpa using this
        rw [Work.Analysis.EndVar.logN, h]
        norm_num
      have h2r : (2 : ℝ) ^ (k' : ℝ) ≤ C * (2 : ℝ) ^ ((l : ℝ) / 4) := by
        rw [Real.rpow_intCast]
        simpa using h2
      have hklogb : (k' : ℝ) ≤ Real.logb 2 C + (l : ℝ) / 4 := by
        have hmono := Real.logb_le_logb_of_le (b := 2) (by norm_num : (1:ℝ) < 2)
          (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) (k' : ℝ)) h2r
        rw [Real.logb_rpow (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) ≠ 1)] at hmono
        rw [logb_two_mul_rpow_quarter C hC l] at hmono
        linarith
      rw [hlogN1]
      have heq : (d : ℝ) * ((l : ℝ) - 1) - 1 = (d : ℝ) * (l : ℝ) - (d : ℝ) - 1 := by ring
      rw [heq]
      linarith
    · have hN2 : 2 ≤ N := by omega
      have hlogN_le := logN_le_logb_two hN2
      have hNpos : (0 : ℝ) < (N : ℝ) := by
        have : (0 : ℕ) < N := by omega
        exact_mod_cast this
      have h2r : (2 : ℝ) ^ (k' : ℝ) ≤ C * (2 : ℝ) ^ ((l : ℝ) / 4) / (N : ℝ) ^ d := by
        rw [Real.rpow_intCast]; exact h2
      have hklogb : (k' : ℝ) ≤
          Real.logb 2 C + (l : ℝ) / 4 - (d : ℝ) * Real.logb 2 (N : ℝ) := by
        have hmono := Real.logb_le_logb_of_le (b := 2) (by norm_num : (1:ℝ) < 2)
          (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) (k' : ℝ)) h2r
        rw [Real.logb_rpow (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) ≠ 1)] at hmono
        rw [Real.logb_div (mul_ne_zero (ne_of_gt hC)
              (ne_of_gt (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) _)))
            (ne_of_gt (pow_pos hNpos d))] at hmono
        rw [logb_two_mul_rpow_quarter C hC l] at hmono
        rw [Real.logb_pow] at hmono
        linarith
      have hd0 : (0 : ℝ) ≤ (d : ℝ) := by positivity
      have hstep : (k' : ℝ) ≤
          Real.logb 2 C + (l : ℝ) / 4 - (d : ℝ) * (Work.Analysis.EndVar.logN N : ℝ) := by
        have hmul := mul_le_mul_of_nonneg_left hlogN_le hd0
        linarith
      have htarget : Real.logb 2 C + (l : ℝ) / 4 - (d : ℝ) * (Work.Analysis.EndVar.logN N : ℝ) ≤
          (d : ℝ) * ((l : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) - 1 := by
        have heq : (d : ℝ) * ((l : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) - 1
            = (d : ℝ) * (l : ℝ) - (d : ℝ) * (Work.Analysis.EndVar.logN N : ℝ) - 1 := by ring
        rw [heq]
        linarith [hgoal2, hd0]
      linarith
  exact_mod_cast hkR

end Work.KMTAreas.A4Z
