import Mathlib.Algebra.Polynomial.Degree.Operations

namespace Commons.Algebra.Polynomial

theorem coeff_mul_natDegree_le_sub_one {R : Type*} [Semiring R] (A B : Polynomial R) (a b : ℕ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hA : A.natDegree ≤ a) (hB : B.natDegree ≤ b) :
    (A * B).coeff (a + b - 1) = A.coeff a * B.coeff (b - 1) + A.coeff (a - 1) * B.coeff b := by
  rw [Polynomial.coeff_mul]
  have hsub : ({(a, b - 1), (a - 1, b)} : Finset (ℕ × ℕ)) ⊆
      Finset.HasAntidiagonal.antidiagonal (a + b - 1) := by
    intro x hx
    rw [Finset.HasAntidiagonal.mem_antidiagonal]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> omega
  have hzero : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal (a + b - 1),
      x ∉ ({(a, b - 1), (a - 1, b)} : Finset (ℕ × ℕ)) →
      A.coeff x.1 * B.coeff x.2 = 0 := by
    intro x hx hxs
    have hsum : x.1 + x.2 = a + b - 1 := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    have hxp : x ≠ (a, b - 1) := by
      intro h; exact hxs (by rw [h]; simp)
    have hxq : x ≠ (a - 1, b) := by
      intro h; exact hxs (by rw [h]; simp)
    have hsplit : a < x.1 ∨ b < x.2 := by
      by_contra hc
      push Not at hc
      obtain ⟨h1, h2⟩ := hc
      have e1 : x.1 = a - 1 ∨ x.1 = a := by omega
      have e2 : x.2 = b - 1 ∨ x.2 = b := by omega
      rcases e1 with h3 | h3 <;> rcases e2 with h4 | h4
      · exfalso; omega
      · exfalso; exact hxq (by ext <;> omega)
      · exfalso; exact hxp (by ext <;> omega)
      · exfalso; omega
    rcases hsplit with hlt | hlt
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hA hlt), zero_mul]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hB hlt), mul_zero]
  trans ∑ x ∈ ({(a, b - 1), (a - 1, b)} : Finset (ℕ × ℕ)), A.coeff x.1 * B.coeff x.2
  · exact (Finset.sum_subset hsub hzero).symm
  · rw [Finset.sum_pair (by intro h; have := congrArg Prod.fst h; simp at this; omega)]

end Commons.Algebra.Polynomial