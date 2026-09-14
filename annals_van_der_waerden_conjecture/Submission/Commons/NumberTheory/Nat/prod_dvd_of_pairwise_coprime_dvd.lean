import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Divisibility.Units
import Mathlib.Data.Nat.GCD.BigOperators

namespace Commons.NumberTheory.Nat

open scoped BigOperators

/-- If finitely many pairwise-coprime natural numbers each divide `h`, then so
does their product. (Degenerate cases are harmless: if some member is `0` then
`0 ∣ h` forces `h = 0`, and pairwise coprimality forces all other members to
be `1`.) -/
theorem prod_dvd_of_pairwise_coprime_dvd {t : Finset ℕ} {h : ℕ}
    (hcop : ∀ p ∈ t, ∀ q ∈ t, p ≠ q → Nat.Coprime p q)
    (hdiv : ∀ p ∈ t, p ∣ h) :
    (∏ p ∈ t, p) ∣ h := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
      have hcop_s : ∀ p ∈ s, ∀ q ∈ s, p ≠ q → Nat.Coprime p q := by
        intro p hp q hq hpq
        exact hcop p (Finset.mem_insert_of_mem hp) q (Finset.mem_insert_of_mem hq) hpq
      have hdiv_s : ∀ p ∈ s, p ∣ h := by
        intro p hp
        exact hdiv p (Finset.mem_insert_of_mem hp)
      have hprod_s : (∏ p ∈ s, p) ∣ h := ih hcop_s hdiv_s
      have ha_dvd : a ∣ h := hdiv a (Finset.mem_insert_self a s)
      have hcop_a_prod : Nat.Coprime a (∏ p ∈ s, p) := by
        exact Nat.Coprime.prod_right (by
          intro q hq
          apply hcop a (Finset.mem_insert_self a s) q (Finset.mem_insert_of_mem hq)
          intro hqa
          exact has (hqa ▸ hq))
      rw [Finset.prod_insert has]
      exact hcop_a_prod.mul_dvd_of_dvd_of_dvd ha_dvd hprod_s

end Commons.NumberTheory.Nat