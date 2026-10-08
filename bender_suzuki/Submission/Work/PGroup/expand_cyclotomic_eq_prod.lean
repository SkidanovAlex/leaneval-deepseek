import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PGroup

open Polynomial

/-- Iterating the prime case `p ∣ n` of the cyclotomic/expand interaction:
`Φ_{n q}(X^{q^j}) = Φ_{n q^{j+1}}(X)`. -/
lemma expand_pow_cyclotomic_mul {q : ℕ} (hq : q.Prime) :
    ∀ n j : ℕ, Polynomial.expand ℤ (q^j) (Polynomial.cyclotomic (n*q) ℤ)
      = Polynomial.cyclotomic (n * q^(j+1)) ℤ := by
  intro n j
  induction j generalizing n with
  | zero => simp
  | succ j ih =>
    conv_lhs => rw [pow_succ]
    rw [Polynomial.expand_mul,
      Polynomial.cyclotomic_expand_eq_cyclotomic hq (dvd_mul_left q n)]
    rw [show n * q ^ (j + 1 + 1) = (n * q) * q ^ (j + 1) by
      rw [mul_assoc, pow_succ' q (j+1)]]
    exact ih (n * q)

/-- For a prime `q` not dividing `n`,
`Φ_n(X^{q^j}) = ∏_{i=0}^{j} Φ_{n q^i}(X)`. -/
lemma expand_cyclotomic_eq_prod_of_not_dvd {q : ℕ} (hq : q.Prime) :
    ∀ n j : ℕ, ¬ q ∣ n →
    Polynomial.expand ℤ (q^j) (Polynomial.cyclotomic n ℤ)
      = ∏ i ∈ Finset.range (j+1), Polynomial.cyclotomic (n * q^i) ℤ := by
  intro n j
  induction j with
  | zero => intro hqn; simp
  | succ j ih =>
    intro hqn
    conv_lhs => rw [pow_succ]
    rw [Polynomial.expand_mul,
      Polynomial.cyclotomic_expand_eq_cyclotomic_mul hq hqn ℤ, map_mul, ih hqn,
      expand_pow_cyclotomic_mul hq n j]
    conv_rhs => rw [Finset.prod_range_succ]
    ring

theorem expand_cyclotomic_eq_prod {q D j : ℕ} (hq : q.Prime) (hDq : ¬ q ∣ D) :
    Polynomial.expand ℤ (q ^ j) (Polynomial.cyclotomic D ℤ)
      = ∏ i ∈ Finset.range (j + 1), Polynomial.cyclotomic (D * q ^ i) ℤ :=
  expand_cyclotomic_eq_prod_of_not_dvd hq D j hDq

end Work.PGroup
