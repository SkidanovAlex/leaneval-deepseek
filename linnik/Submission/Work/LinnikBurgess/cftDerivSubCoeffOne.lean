import Mathlib

namespace Work.LinnikBurgess

/-- If an integer `c` divides every coefficient of an integral polynomial `P`, then it divides
every value of `P` at an integer. -/
lemma cft_dvd_eval_of_dvd_coeff {c : ℤ} {P : Polynomial ℤ} (h : ∀ n, c ∣ P.coeff n) (x : ℤ) :
    c ∣ P.eval x := by
  obtain ⟨Q, hQ⟩ := (Polynomial.C_dvd_iff_dvd_coeff c P).mpr h
  rw [hQ, Polynomial.eval_mul, Polynomial.eval_C]
  exact dvd_mul_right c _

/-- If a natural number `p` divides every coefficient of `G : ℤ[X]` of index `≥ 2`, then `p`
divides `G'(x) - G.coeff 1` for every integer `x`: the derivative evaluated at `x` equals
`G.coeff 1` plus a sum of terms `i * G.coeff i * x^{i-1}` with `i ≥ 2`, each divisible by `p`. -/
lemma cftDerivSubCoeffOne {p : ℕ} (G : Polynomial ℤ)
    (h : ∀ i, 2 ≤ i → (p : ℤ) ∣ G.coeff i) (x : ℤ) :
    (p : ℤ) ∣ (G.derivative.eval x - G.coeff 1) := by
  have hQ : ∀ n, (p : ℤ) ∣ (G.derivative - Polynomial.C (G.coeff 1)).coeff n := by
    intro n
    rw [Polynomial.coeff_sub, Polynomial.coeff_derivative]
    rcases eq_or_ne n 0 with h0 | h0
    · subst h0
      simp
    · rw [Polynomial.coeff_C, if_neg h0, sub_zero]
      exact dvd_mul_of_dvd_left (h (n + 1) (by omega)) _
  have := cft_dvd_eval_of_dvd_coeff hQ x
  rwa [Polynomial.eval_sub, Polynomial.eval_C] at this

end Work.LinnikBurgess
