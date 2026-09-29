import Mathlib

namespace Work.C17adj

open Polynomial

/-- If `a.natDegree ≤ i` and `b.natDegree ≤ j`, then the coefficient of `a * b` in degree
`i + j` is the product of the coefficients in degrees `i` and `j`: all other terms of the
Cauchy product vanish. -/
private lemma coeff_mul_eq_of_natDegree_le {a b : Polynomial ℂ} {i j : ℕ}
    (ha : a.natDegree ≤ i) (hb : b.natDegree ≤ j) :
    (a * b).coeff (i + j) = a.coeff i * b.coeff j := by
  rw [coeff_mul]
  refine Finset.sum_eq_single (i, j) ?_ ?_
  · rintro ⟨x, y⟩ hmem hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hmem
    rcases lt_trichotomy x i with hlt | heq | hgt
    · have hy : j < y := by omega
      rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hb hy), mul_zero]
    · have hy : y = j := by omega
      exact absurd (by simp [heq, hy]) hne
    · have hx : a.natDegree < x := lt_of_le_of_lt ha hgt
      rw [coeff_eq_zero_of_natDegree_lt hx, zero_mul]
  · intro h
    exact absurd (by simp : (i, j) ∈ Finset.HasAntidiagonal.antidiagonal (i + j)) h

theorem deriv_mul_le (p q : Polynomial ℂ) (hq : q.natDegree ≤ 26) :
    (p.derivative * q).natDegree ≤ p.natDegree + 25 ∧
      (p.derivative * q).coeff (p.natDegree + 25)
        = (p.natDegree : ℂ) * p.leadingCoeff * q.coeff 26 := by
  by_cases hp : p.natDegree = 0
  · rw [derivative_of_natDegree_zero hp, hp]
    simp
  · have hn : 0 < p.natDegree := Nat.pos_of_ne_zero hp
    have hnd : p.derivative.natDegree = p.natDegree - 1 := natDegree_derivative p
    refine ⟨?_, ?_⟩
    · calc (p.derivative * q).natDegree
          ≤ p.derivative.natDegree + q.natDegree := natDegree_mul_le
        _ ≤ (p.natDegree - 1) + 26 := add_le_add (natDegree_derivative_le p) hq
        _ ≤ p.natDegree + 25 := by omega
    · have h1 : (p.derivative * q).coeff ((p.natDegree - 1) + 26)
          = (p.derivative).coeff (p.natDegree - 1) * q.coeff 26 :=
        coeff_mul_eq_of_natDegree_le (le_of_eq hnd) hq
      have h2 : (p.derivative).coeff (p.natDegree - 1)
          = p.leadingCoeff * (p.natDegree : ℂ) := by
        rw [← hnd, coeff_natDegree, leadingCoeff_derivative]
      have hsub : (p.natDegree - 1) + 26 = p.natDegree + 25 := by omega
      rw [hsub] at h1
      rw [h1, h2]
      ring

end Work.C17adj
