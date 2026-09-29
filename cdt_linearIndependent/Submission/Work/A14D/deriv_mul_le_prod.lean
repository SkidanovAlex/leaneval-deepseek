import Mathlib

namespace Work.A14D

theorem deriv_mul_le_prod (p q : Polynomial ℂ) (s : ℕ) (hq : q.natDegree ≤ s + 1) :
    (p.derivative * q).natDegree ≤ p.natDegree + s ∧
      (p.derivative * q).coeff (p.natDegree + s)
        = (p.natDegree : ℂ) * p.leadingCoeff * q.coeff (s + 1) := by
  rcases Nat.eq_zero_or_pos p.natDegree with hn0 | hn
  · -- p is a constant, so p.derivative = 0
    have hp : p = Polynomial.C (p.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hn0
    rw [hp]
    simp
  · -- p has positive degree
    have hder_le : ∀ i, p.natDegree ≤ i → p.derivative.coeff i = 0 := by
      intro i hi
      rw [Polynomial.coeff_derivative]
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
    -- the leading coefficient of the derivative
    have hder_top : p.derivative.coeff (p.natDegree - 1)
        = (p.natDegree : ℂ) * p.leadingCoeff := by
      rw [Polynomial.coeff_derivative, Nat.sub_add_cancel hn, Polynomial.coeff_natDegree]
      have h2 : ((p.natDegree - 1 : ℕ) : ℂ) + 1 = (p.natDegree : ℂ) := by
        conv_rhs => rw [← Nat.sub_add_cancel hn]
        rw [Nat.cast_add, Nat.cast_one]
      rw [h2, mul_comm]
    have hmem : (p.natDegree - 1, s + 1) ∈
        Finset.HasAntidiagonal.antidiagonal (p.natDegree + s) := by
      rw [Finset.HasAntidiagonal.mem_antidiagonal]
      omega
    -- only the pair (n-1, s+1) contributes to the top coefficient
    have hsum : ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (p.natDegree + s),
        p.derivative.coeff x.1 * q.coeff x.2
        = p.derivative.coeff (p.natDegree - 1) * q.coeff (s + 1) := by
      apply Finset.sum_eq_single (p.natDegree - 1, s + 1)
      · rintro ⟨b1, b2⟩ hb hne
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hb
        by_cases h1 : p.natDegree ≤ b1
        · rw [hder_le b1 h1, zero_mul]
        · rw [not_le] at h1
          have hb2 : s + 1 ≤ b2 := by omega
          rcases lt_or_eq_of_le hb2 with h2 | h2
          · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (p := q) (n := b2)
              (lt_of_le_of_lt hq h2), mul_zero]
          · exfalso
            have : b1 = p.natDegree - 1 := by omega
            exact hne (by simp [this, h2])
      · intro h
        exact absurd hmem h
    constructor
    · calc (p.derivative * q).natDegree
            ≤ p.derivative.natDegree + q.natDegree := Polynomial.natDegree_mul_le
        _ ≤ (p.natDegree - 1) + (s + 1) :=
              add_le_add (Polynomial.natDegree_derivative_le p) hq
        _ = p.natDegree + s := by omega
    · rw [Polynomial.coeff_mul, hsum, hder_top]

end Work.A14D
