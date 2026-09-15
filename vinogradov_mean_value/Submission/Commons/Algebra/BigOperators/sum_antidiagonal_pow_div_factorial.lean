import Mathlib

namespace Commons.Algebra.BigOperators

theorem sum_antidiagonal_pow_div_factorial {F : Type*} [Field F] [CharZero F]
    (n : ℕ) (x y : F) :
    (Finset.HasAntidiagonal.antidiagonal n).sum (fun kl : ℕ × ℕ =>
      (x ^ kl.1 / ((kl.1.factorial : ℕ) : F)) * (y ^ kl.2 / ((kl.2.factorial : ℕ) : F)))
      = (x + y) ^ n / ((n.factorial : ℕ) : F) := by
  rw [eq_div_iff (Nat.cast_ne_zero.mpr n.factorial_ne_zero)]
  rw [Finset.sum_mul]
  trans ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
      ((n.choose kl.1 : ℕ) : F) * (x ^ kl.1 * y ^ kl.2)
  · apply Finset.sum_congr rfl
    intro kl hkl
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hkl
    have hfac_nat : n.choose kl.1 * kl.1.factorial * kl.2.factorial = n.factorial := by
      rw [Nat.choose_symm_of_eq_add hkl.symm, ← hkl]
      exact Nat.add_choose_mul_factorial_mul_factorial kl.1 kl.2
    have hfac : ((n.choose kl.1 : ℕ) : F) * ((kl.1.factorial : ℕ) : F) *
        ((kl.2.factorial : ℕ) : F) = ((n.factorial : ℕ) : F) := by
      rw [← Nat.cast_mul, ← Nat.cast_mul, hfac_nat]
    rw [← hfac]
    have hA : ((kl.1.factorial : ℕ) : F) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero kl.1
    have hB : ((kl.2.factorial : ℕ) : F) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero kl.2
    field_simp
  · rw [Commute.add_pow' (Commute.all x y) n]
    apply Finset.sum_congr rfl
    intro kl hkl
    rw [nsmul_eq_mul]

end Commons.Algebra.BigOperators
