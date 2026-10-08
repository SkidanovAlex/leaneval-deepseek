import Mathlib
import Submission.Work.Higman.Q3.two_pow_add_eq_two_pow
import Submission.Work.Higman.Q3.two_pow_add_add_one_eq

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman.Q3

/-- Bounds plus divisibility.  With `A, B, C < n` and `1 ≤ n`, the integer
`X = 2^A + 2^B - 2^C` satisfies `-(2^n - 1) < X ≤ 2^n - 1`; since the divisor `2^n - 1` is
positive, the only multiples of it in that interval are `0` and `2^n - 1`. -/
private theorem dvd_two_pow_sub_one_eq_zero_or_eq {n A B C : ℕ} (hn : 1 ≤ n)
    (hA : A < n) (hB : B < n) (hC : C < n)
    (h : (2 ^ n - 1 : ℤ) ∣ (2 ^ A : ℤ) + 2 ^ B - 2 ^ C) :
    (2 ^ A : ℤ) + 2 ^ B - 2 ^ C = 0 ∨ (2 ^ A : ℤ) + 2 ^ B - 2 ^ C = (2 ^ n - 1 : ℤ) := by
  have hAn : A ≤ n - 1 := by omega
  have hBn : B ≤ n - 1 := by omega
  have hCn : C ≤ n - 1 := by omega
  have hpowA : (2 : ℤ) ^ A ≤ (2 : ℤ) ^ (n - 1) := pow_le_pow_right₀ (by norm_num) hAn
  have hpowB : (2 : ℤ) ^ B ≤ (2 : ℤ) ^ (n - 1) := pow_le_pow_right₀ (by norm_num) hBn
  have hpowC : (2 : ℤ) ^ C ≤ (2 : ℤ) ^ (n - 1) := pow_le_pow_right₀ (by norm_num) hCn
  have hpowC1 : (1 : ℤ) ≤ (2 : ℤ) ^ C := one_le_pow₀ (by norm_num)
  have hpowA1 : (1 : ℤ) ≤ (2 : ℤ) ^ A := one_le_pow₀ (by norm_num)
  have hpowB1 : (1 : ℤ) ≤ (2 : ℤ) ^ B := one_le_pow₀ (by norm_num)
  have h2n : (2 : ℤ) ^ n = (2 : ℤ) ^ (n - 1) * 2 := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    rw [pow_succ]
  have hnn : (0 : ℤ) ≤ (2 : ℤ) ^ (n - 1) := pow_nonneg (by norm_num) _
  have hle : (2 : ℤ) ^ A + (2 : ℤ) ^ B - (2 : ℤ) ^ C ≤ (2 : ℤ) ^ n - 1 := by linarith
  have hgt : -((2 : ℤ) ^ n - 1) < (2 : ℤ) ^ A + (2 : ℤ) ^ B - (2 : ℤ) ^ C := by linarith
  have hDpos : (0 : ℤ) < (2 : ℤ) ^ n - 1 := by
    have h2 : (2 : ℤ) ^ 1 ≤ (2 : ℤ) ^ n := pow_le_pow_right₀ (by norm_num) hn
    norm_num at h2
    linarith
  obtain ⟨k, hk⟩ := h
  have hk_le : k ≤ 1 := by
    have h' : k * ((2 : ℤ) ^ n - 1) ≤ 1 * ((2 : ℤ) ^ n - 1) := by
      rw [one_mul, mul_comm k, ← hk]; exact hle
    exact (mul_le_mul_iff_left₀ hDpos).mp h'
  have hk_gt : -1 < k := by
    have h' : (-1) * ((2 : ℤ) ^ n - 1) < k * ((2 : ℤ) ^ n - 1) := by
      rw [neg_one_mul, mul_comm k, ← hk]; exact hgt
    exact (mul_lt_mul_iff_left₀ hDpos).mp h'
  rcases (by omega : k = 0 ∨ k = 1) with hk0 | hk1
  · left; rw [hk, hk0, mul_zero]
  · right; rw [hk, hk1, mul_one]

theorem two_pow_add_eq_pow {n A B C : ℕ} (hn : 1 ≤ n) (hA : A < n) (hB : B < n) (hC : C < n)
    (h : (2 ^ n - 1 : ℤ) ∣ (2 ^ A : ℤ) + 2 ^ B - 2 ^ C) :
    A = B ∧ (A + 1 = C ∨ (A + 1 = n ∧ C = 0)) := by
  rcases dvd_two_pow_sub_one_eq_zero_or_eq hn hA hB hC h with h0 | hd
  · have hnat : 2 ^ A + 2 ^ B = 2 ^ C := by
      have h1 : ((2 ^ A + 2 ^ B : ℕ) : ℤ) = ((2 ^ C : ℕ) : ℤ) := by
        push_cast
        linarith [h0]
      exact_mod_cast h1
    obtain ⟨hAB, hC'⟩ := two_pow_add_eq_two_pow hnat
    exact ⟨hAB, Or.inl hC'.symm⟩
  · have hnat : 2 ^ A + 2 ^ B + 1 = 2 ^ C + 2 ^ n := by
      have h1 : ((2 ^ A + 2 ^ B + 1 : ℕ) : ℤ) = ((2 ^ C + 2 ^ n : ℕ) : ℤ) := by
        push_cast
        linarith [hd]
      exact_mod_cast h1
    obtain ⟨hAB, hC0, hAn⟩ := two_pow_add_add_one_eq hn hA hB hC hnat
    exact ⟨hAB, Or.inr ⟨hAn, hC0⟩⟩

end Work.Higman.Q3
