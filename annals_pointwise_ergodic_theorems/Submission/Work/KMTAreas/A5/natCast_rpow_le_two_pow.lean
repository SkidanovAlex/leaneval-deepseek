import Mathlib
import Submission.Work.Analysis.EndVar.Defs

namespace Work.KMTAreas.A5

/-- For every `P ≥ 0` and `ε > 0` there is a constant `C ≥ 0` with
`n ^ P ≤ C * 2 ^ (ε * n)` for all `n : ℕ`.  Polynomial growth is absorbed by an
arbitrarily slow exponential growth.

The proof takes `k = ⌈P⌉₊` and `C = max 1 (k! / (ε * log 2) ^ k)`.  For `n ≥ 1`
one has `n ^ P ≤ n ^ k`, and the elementary bound `x ^ k / k! ≤ exp x` at
`x = ε * log 2 * n` gives `n ^ k ≤ (k! / (ε * log 2) ^ k) * 2 ^ (ε * n)`.  The
initial segment `n ≤ 1` is handled by the `max 1`. -/
theorem natCast_rpow_le_two_pow {P ε : ℝ} (hP : 0 ≤ P) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, (n : ℝ) ^ P ≤ C * (2 : ℝ) ^ (ε * (n : ℝ)) := by
  set k : ℕ := Nat.ceil P with hkdef
  have hPk : P ≤ (k : ℝ) := by rw [hkdef]; exact Nat.le_ceil P
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbase : 0 < ε * Real.log 2 := mul_pos hε hlog2
  set C : ℝ := max 1 ((k.factorial : ℝ) / (ε * Real.log 2) ^ k) with hCdef
  refine ⟨C, ?_, ?_⟩
  · rw [hCdef]; exact le_max_of_le_left (by norm_num)
  · intro n
    have hC1 : (1:ℝ) ≤ C := by rw [hCdef]; exact le_max_left _ _
    have hC0le : (k.factorial : ℝ) / (ε * Real.log 2) ^ k ≤ C := by
      rw [hCdef]; exact le_max_right _ _
    have hCn : (0:ℝ) ≤ C := le_trans zero_le_one hC1
    have hnnonneg : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    have hpow2 : (1:ℝ) ≤ (2:ℝ) ^ (ε * (n:ℝ)) :=
      Real.one_le_rpow (by norm_num) (mul_nonneg hε.le hnnonneg)
    -- the polynomial/`max` bound on the initial segment
    have hA : (n:ℝ)^P ≤ max 1 ((n:ℝ)^k) := by
      rcases lt_or_ge (n:ℝ) 1 with h | h
      · have hle : (n:ℝ)^P ≤ 1 := Real.rpow_le_one hnnonneg (le_of_lt h) hP
        exact le_trans hle (le_max_left _ _)
      · have hle : (n:ℝ)^P ≤ (n:ℝ)^(k:ℝ) := Real.rpow_le_rpow_of_exponent_le h hPk
        rw [Real.rpow_natCast] at hle
        exact le_trans hle (le_max_right _ _)
    -- the exponential bound from `x ^ k / k! ≤ exp x`
    have h1 : (ε * Real.log 2)^k * (n:ℝ)^k / (k.factorial:ℝ) ≤ (2:ℝ)^(ε*(n:ℝ)) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
      have key := Real.pow_div_factorial_le_exp ((ε * Real.log 2) * (n:ℝ))
        (mul_nonneg (mul_nonneg hε.le hlog2.le) hnnonneg) k
      rw [mul_pow] at key
      rw [show (ε * Real.log 2) * (n:ℝ) = Real.log 2 * (ε * (n:ℝ)) by ring] at key
      exact key
    have hb : (0:ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
    have ha : (0:ℝ) < (ε * Real.log 2)^k := pow_pos hbase k
    have h2 : (n:ℝ)^k ≤ (k.factorial : ℝ)/(ε*Real.log 2)^k * (2:ℝ)^(ε*(n:ℝ)) := by
      have hmul := mul_le_mul_of_nonneg_left h1 (le_of_lt (div_pos hb ha))
      have hba : ((k.factorial:ℝ)/(ε*Real.log 2)^k) *
          ((ε*Real.log 2)^k * (n:ℝ)^k / (k.factorial:ℝ)) = (n:ℝ)^k := by
        field_simp
      rwa [hba] at hmul
    have h3 : (k.factorial:ℝ)/(ε*Real.log 2)^k * (2:ℝ)^(ε*(n:ℝ)) ≤
        C * (2:ℝ)^(ε*(n:ℝ)) :=
      mul_le_mul_of_nonneg_right hC0le (by positivity)
    have hB1 : (1:ℝ) ≤ C * (2:ℝ)^(ε*(n:ℝ)) := by
      have := mul_le_mul hC1 hpow2 (by norm_num : (0:ℝ) ≤ 1) hCn
      simpa using this
    have hB2 : (n:ℝ)^k ≤ C * (2:ℝ)^(ε*(n:ℝ)) := le_trans h2 h3
    exact le_trans hA (max_le hB1 hB2)

end Work.KMTAreas.A5
