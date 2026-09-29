import Mathlib

namespace Work.A14D

open Polynomial

/-- Coefficient of a second derivative. -/
lemma coeff_deriv2 (p : Polynomial ℂ) (k : ℕ) :
    p.derivative.derivative.coeff k = p.coeff (k + 2) * ((k : ℂ) + 2) * ((k : ℂ) + 1) := by
  rw [Polynomial.coeff_derivative, Polynomial.coeff_derivative]
  push_cast
  ring

theorem deriv2_mul_le_prod (p q : Polynomial ℂ) (s : ℕ) (hq : q.natDegree ≤ s + 2) :
    (p.derivative.derivative * q).natDegree ≤ p.natDegree + s ∧
      (p.derivative.derivative * q).coeff (p.natDegree + s)
        = (p.natDegree : ℂ) * ((p.natDegree : ℂ) - 1) * p.leadingCoeff * q.coeff (s + 2) := by
  by_cases h2 : 2 ≤ p.natDegree
  · obtain ⟨n', hn'⟩ : ∃ n', p.natDegree = n' + 2 := ⟨p.natDegree - 2, by omega⟩
    have key1 : p.derivative.derivative.natDegree ≤ n' := by
      have hA : p.derivative.derivative.natDegree ≤ (p.derivative).natDegree - 1 :=
        Polynomial.natDegree_derivative_le (p.derivative)
      have hB : (p.derivative).natDegree ≤ n' + 1 := by
        have h := Polynomial.natDegree_derivative_le p
        omega
      omega
    have hcoeff : (p.derivative.derivative * q).coeff (p.natDegree + s)
        = p.derivative.derivative.coeff n' * q.coeff (s + 2) := by
      have hidx : p.natDegree + s = (n' + 2) + s := by omega
      rw [hidx, Polynomial.coeff_mul]
      refine Finset.sum_eq_single (n', s + 2) ?_ ?_
      · rintro ⟨b1, b2⟩ hb hbne
        have hbsum : b1 + b2 = (n' + 2) + s := by
          simpa using (Finset.HasAntidiagonal.mem_antidiagonal.mp hb)
        rcases Nat.lt_trichotomy b1 n' with h | h | h
        · have hlt : q.natDegree < b2 := by omega
          rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt, mul_zero]
        · exfalso
          have hb2 : b2 = s + 2 := by omega
          exact hbne (by simp [h, hb2])
        · have hlt : p.derivative.derivative.natDegree < b1 := by omega
          rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt, zero_mul]
      · intro hmem
        exact absurd hmem (by rw [Finset.HasAntidiagonal.mem_antidiagonal]; omega)
    constructor
    · have h := Polynomial.natDegree_mul_le (p := p.derivative.derivative) (q := q)
      omega
    · have hb : p.derivative.derivative.coeff n'
          = (p.natDegree : ℂ) * ((p.natDegree : ℂ) - 1) * p.leadingCoeff := by
        rw [coeff_deriv2]
        have hpcoeff : p.coeff (n' + 2) = p.leadingCoeff := by
          rw [← Polynomial.coeff_natDegree, hn']
        have hc1 : ((n' : ℂ) + 2) = (p.natDegree : ℂ) := by rw [hn']; push_cast; ring
        have hc2 : ((n' : ℂ) + 1) = (p.natDegree : ℂ) - 1 := by rw [hn']; push_cast; ring
        rw [hpcoeff, hc1, hc2]
        ring
      rw [hcoeff, hb]
  · have hle : p.natDegree ≤ 1 := by omega
    have hder : p.derivative.derivative = 0 := by
      apply (Polynomial.derivative_eq_zero).mpr
      have h := Polynomial.natDegree_derivative_le p
      omega
    have hzero : (p.natDegree : ℂ) * ((p.natDegree : ℂ) - 1) = 0 := by
      rcases (by omega : p.natDegree = 0 ∨ p.natDegree = 1) with h | h <;> rw [h] <;> norm_num
    exact ⟨by simp [hder], by simp [hder, hzero]⟩

end Work.A14D
