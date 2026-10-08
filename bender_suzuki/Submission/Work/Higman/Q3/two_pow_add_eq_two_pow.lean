import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman.Q3

/-- If a sum of two powers of two is itself a power of two, the two exponents are equal and the
resulting exponent is one more.  Elementary: writing `A ≤ B`, `2^C = 2^A + 2^B` lies strictly
between `2^B` and `2^(B+1)`, so `C = B + 1`, and then `2^A = 2^B`. -/
theorem two_pow_add_eq_two_pow {A B C : ℕ} (h : 2 ^ A + 2 ^ B = 2 ^ C) :
    A = B ∧ C = A + 1 := by
  rcases le_total A B with hAB | hBA
  · have hBlt : 2 ^ B < 2 ^ C := by
      have : 2 ^ B < 2 ^ A + 2 ^ B := Nat.lt_add_of_pos_left (Nat.two_pow_pos A)
      rwa [h] at this
    have hBC : B < C := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hBlt
    have hCle : C ≤ B + 1 := by
      have hle : 2 ^ C ≤ 2 ^ (B + 1) := by
        rw [← h, pow_succ]
        have : 2 ^ A ≤ 2 ^ B := Nat.pow_le_pow_right (by norm_num) hAB
        linarith
      exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
    have hC : C = B + 1 := by omega
    have hABeq : 2 ^ A = 2 ^ B := by
      have : 2 ^ A + 2 ^ B = 2 ^ B + 2 ^ B := by rw [h, hC, pow_succ]; ring
      exact Nat.add_right_cancel this
    have hAB' : A = B := Nat.pow_right_injective (le_refl 2) hABeq
    exact ⟨hAB', by omega⟩
  · have hAlt : 2 ^ A < 2 ^ C := by
      have : 2 ^ A < 2 ^ A + 2 ^ B := Nat.lt_add_of_pos_right (Nat.two_pow_pos B)
      rwa [h] at this
    have hAC : A < C := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hAlt
    have hCle : C ≤ A + 1 := by
      have hle : 2 ^ C ≤ 2 ^ (A + 1) := by
        rw [← h, pow_succ]
        have : 2 ^ B ≤ 2 ^ A := Nat.pow_le_pow_right (by norm_num) hBA
        linarith
      exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
    have hC : C = A + 1 := by omega
    have hBAeq : 2 ^ B = 2 ^ A := by
      have : 2 ^ A + 2 ^ B = 2 ^ A + 2 ^ A := by rw [h, hC, pow_succ]; ring
      exact Nat.add_left_cancel this
    have hAB' : A = B := (Nat.pow_right_injective (le_refl 2) hBAeq).symm
    exact ⟨hAB', by omega⟩

end Work.Higman.Q3
