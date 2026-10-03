import Mathlib
import Submission.Work.KMTAreas.A7.randSymbG_aux

namespace Work.KMTAreas.A7

noncomputable section

open Work.Analysis.EndVar (logN logN_mono)

/-- The elementary bound `N ≤ 2 · 2^{Log N}` behind the `d`-th power estimate on `gScale`. -/
private lemma le_two_mul_two_zpow_logN (N : ℕ) : (N : ℝ) ≤ 2 * (2 : ℝ) ^ (logN N) := by
  have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (max N 2)
  have hN : N ≤ 2 ^ (Nat.log 2 (max N 2) + 1) :=
    le_trans (le_max_left N 2) (le_of_lt h)
  have hNr : (N : ℝ) ≤ (2 : ℝ) ^ (Nat.log 2 (max N 2) + 1) := by
    have : (N : ℝ) ≤ (((2 : ℕ) ^ (Nat.log 2 (max N 2) + 1) : ℕ) : ℝ) := by
      exact_mod_cast hN
    simpa using this
  rw [logN, zpow_natCast]
  calc (N : ℝ) ≤ (2 : ℝ) ^ (Nat.log 2 (max N 2) + 1) := hNr
    _ = 2 * (2 : ℝ) ^ (Nat.log 2 (max N 2)) := by rw [pow_succ]; ring

theorem gScale_arith (d : ℕ) :
    (∀ N k₂ : ℕ, 0 < gScale d N k₂) ∧
    (∀ N N' k₂ : ℕ, N ≤ N' → gScale d N k₂ ≤ gScale d N' k₂) ∧
    (∀ N k₂ : ℕ, gScale d N k₂ = gScale d N 0 * (2 : ℝ) ^ (-((d * k₂ : ℕ) : ℤ))) ∧
    (∀ N k₂ : ℕ, (N : ℝ) ^ d ≤ (2 : ℝ) ^ d * (2 : ℝ) ^ (d * k₂) * gScale d N k₂) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro N k₂
    simp only [gScale]
    exact zpow_pos (by norm_num) _
  · intro N N' k₂ hNN'
    simp only [gScale]
    have hle : logN N - (k₂ : ℤ) ≤ logN N' - (k₂ : ℤ) := by
      have := logN_mono hNN'; omega
    exact zpow_le_zpow_right₀ (by norm_num)
      (mul_le_mul_of_nonneg_left hle (Int.natCast_nonneg d))
  · intro N k₂
    simp only [gScale]
    have hexp : (d : ℤ) * (logN N - (k₂ : ℤ))
        = (d : ℤ) * (logN N - ((0 : ℕ) : ℤ)) + (-((d * k₂ : ℕ) : ℤ)) := by
      push_cast
      ring
    rw [hexp, zpow_add₀ (show (2 : ℝ) ≠ 0 by norm_num)]
  · intro N k₂
    have hmul : ((2 : ℝ) ^ (logN N)) ^ d = (2 : ℝ) ^ ((d : ℤ) * logN N) := by
      rw [← zpow_natCast ((2 : ℝ) ^ (logN N)) d, ← zpow_mul]
      congr 1
      ring
    have hRHS : (2 : ℝ) ^ d * (2 : ℝ) ^ (d * k₂) * gScale d N k₂
        = (2 : ℝ) ^ d * (2 : ℝ) ^ ((d : ℤ) * logN N) := by
      rw [gScale]
      have step : (2 : ℝ) ^ (d * k₂) * (2 : ℝ) ^ ((d : ℤ) * (logN N - (k₂ : ℤ)))
          = (2 : ℝ) ^ ((d : ℤ) * logN N) := by
        rw [← zpow_natCast (2 : ℝ) (d * k₂),
          ← zpow_add₀ (show (2 : ℝ) ≠ 0 by norm_num)]
        congr 1
        push_cast
        ring
      calc (2 : ℝ) ^ d * (2 : ℝ) ^ (d * k₂)
              * (2 : ℝ) ^ ((d : ℤ) * (logN N - (k₂ : ℤ)))
          = (2 : ℝ) ^ d * ((2 : ℝ) ^ (d * k₂)
              * (2 : ℝ) ^ ((d : ℤ) * (logN N - (k₂ : ℤ)))) := by ring
        _ = (2 : ℝ) ^ d * (2 : ℝ) ^ ((d : ℤ) * logN N) := by rw [step]
    rw [hRHS]
    have hpow : (N : ℝ) ^ d ≤ (2 * (2 : ℝ) ^ (logN N)) ^ d :=
      pow_le_pow_left₀ (by positivity) (le_two_mul_two_zpow_logN N) d
    rw [mul_pow] at hpow
    rw [hmul] at hpow
    exact hpow

end

end Work.KMTAreas.A7
