import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Algebra.Order.Ring.Star
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A small lower bound for the Euler totient

We prove `15 n ≤ 4·φ n·(n + 4)` for every `n ≠ 2, 6`.  The argument splits
according to whether `n` has a prime divisor `≥ 5`:

* if it does, say `q | n` with `q.Prime` and `5 ≤ q`, then
  `φ q = q - 1 ≥ 4` divides `φ n`, so `φ n ≥ 4`, and `4·φ n·(n+4) ≥ 16(n+4) ≥ 15n`;
* otherwise every prime divisor of `n` is `2` or `3`, whence `n ≤ 3·φ n`
  (Euler's product formula), and for `n ≥ 8` one gets
  `15n ≤ 45n/3 ≤ 4·φ n·(n+4)`, the remaining `n ≤ 7` being checked directly.
-/

namespace Commons.NumberTheory.Totient

open scoped Nat BigOperators
open Finset Nat

/-- A set of naturals contained in `{2,3}` equals one of `∅`, `{2}`, `{3}`, `{2,3}`. -/
private lemma subset_two_three_cases {S : Finset ℕ} (hS : S ⊆ ({2, 3} : Finset ℕ)) :
    S = ∅ ∨ S = ({2} : Finset ℕ) ∨ S = ({3} : Finset ℕ) ∨ S = ({2, 3} : Finset ℕ) := by
  classical
  by_cases h2 : (2 : ℕ) ∈ S
  · by_cases h3 : (3 : ℕ) ∈ S
    · refine Or.inr (Or.inr (Or.inr ?_))
      ext p
      constructor
      · intro hp
        have hp23 := hS hp
        simp at hp23
        rcases hp23 with h | h
        · rw [h]
          simp
        · rw [h]
          simp
      · intro hp
        simp at hp
        rcases hp with h | h
        · rw [h]
          exact h2
        · rw [h]
          exact h3
    · refine Or.inr (Or.inl ?_)
      ext p
      constructor
      · intro hp
        have hp23 := hS hp
        simp at hp23
        rcases hp23 with h | h
        · simp [h]
        · rw [h] at hp
          exfalso
          exact h3 hp
      · intro hp
        simp at hp
        rw [hp]
        exact h2
  · by_cases h3 : (3 : ℕ) ∈ S
    · refine Or.inr (Or.inr (Or.inl ?_))
      ext p
      constructor
      · intro hp
        have hp23 := hS hp
        simp at hp23
        rcases hp23 with h | h
        · rw [h] at hp
          exfalso
          exact h2 hp
        · simp [h]
      · intro hp
        simp at hp
        rw [hp]
        exact h3
    · refine Or.inl ?_
      ext p
      constructor
      · intro hp
        exfalso
        have hp23 := hS hp
        simp at hp23
        rcases hp23 with h | h
        · rw [h] at hp
          exact h2 hp
        · rw [h] at hp
          exact h3 hp
      · intro hp
        simp at hp

/-- If every prime divisor of `m` is at most `3`, then `3·φ m ≥ m`. -/
private lemma le_three_mul_totient_of_primes_le_three (m : ℕ) (hm : 0 < m)
    (hsmall : ∀ q : ℕ, q.Prime → q ∣ m → q ≤ 3) : m ≤ 3 * φ m := by
  classical
  have hne : m ≠ 0 := ne_of_gt hm
  have hSR : m.primeFactors ⊆ ({2, 3} : Finset ℕ) := by
    intro p hp
    have hpm := (Nat.mem_primeFactors).mp hp
    have hle : p ≤ 3 := hsmall p hpm.1 hpm.2.1
    have hp2 : 2 ≤ p := hpm.1.two_le
    have hp23 : p = 2 ∨ p = 3 := by omega
    simp [hp23]
  have hRQ : m.primeFactors.prod (fun p : ℕ => p) ≤
      3 * m.primeFactors.prod (fun p : ℕ => p - 1) := by
    rcases subset_two_three_cases hSR with hS | hS | hS | hS
    · rw [hS]
      norm_num
    · rw [hS]
      norm_num
    · rw [hS]
      norm_num
    · rw [hS]
      norm_num
  have htot : φ m * m.primeFactors.prod (fun p : ℕ => p) =
      m * m.primeFactors.prod (fun p : ℕ => p - 1) := Nat.totient_mul_prod_primeFactors m
  have hRpos : 0 < m.primeFactors.prod (fun p : ℕ => p) := by
    exact Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
  apply Nat.le_of_mul_le_mul_right _ hRpos
  calc
    m * m.primeFactors.prod (fun p : ℕ => p)
        ≤ m * (3 * m.primeFactors.prod (fun p : ℕ => p - 1)) :=
          Nat.mul_le_mul_left m hRQ
    _ = 3 * φ m * m.primeFactors.prod (fun p : ℕ => p) := by
      calc
        m * (3 * m.primeFactors.prod (fun p : ℕ => p - 1)) =
            3 * (m * m.primeFactors.prod (fun p : ℕ => p - 1)) := by ring
        _ = 3 * (φ m * m.primeFactors.prod (fun p : ℕ => p)) := by rw [htot]
        _ = 3 * φ m * m.primeFactors.prod (fun p : ℕ => p) := by ring

/-- If `n ∉ {2,6}` then `15 n ≤ 4·φ n·(n+4)`. -/
theorem totient_bound_K (n : ℕ) (hn2 : n ≠ 2) (hn6 : n ≠ 6) : 15 * n ≤ 4 * φ n * (n + 4) := by
  by_cases hn0 : n = 0
  · subst n
    norm_num
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  by_cases hbig : ∃ q : ℕ, q.Prime ∧ 5 ≤ q ∧ q ∣ n
  · rcases hbig with ⟨q, hqp, hq5, hqd⟩
    have hdv : φ q ∣ φ n := Nat.totient_dvd_of_dvd hqd
    have hphipos : 0 < φ n := Nat.totient_pos.mpr hnpos
    have hφq : φ q = q - 1 := Nat.totient_prime hqp
    have hqphi4 : 4 ≤ φ n := by
      have h4q : 4 ≤ φ q := by
        rw [hφq]
        omega
      exact le_trans h4q (le_of_dvd hphipos hdv)
    have h16 : 16 ≤ 4 * φ n := by omega
    calc
      15 * n ≤ 16 * (n + 4) := by omega
      _ ≤ 4 * φ n * (n + 4) := by
        exact mul_le_mul_right (n + 4) h16
  · have hsmall : ∀ q : ℕ, q.Prime → q ∣ n → q ≤ 3 := by
      intro q hqp hqd
      by_contra hnot
      have hq5 : 5 ≤ q := by
        by_contra hq5'
        have hqge4 : 4 ≤ q := by omega
        have hqle4 : q ≤ 4 := by omega
        have hq4 : q = 4 := by omega
        subst q
        norm_num at hqp
      exact hbig ⟨q, hqp, hq5, hqd⟩
    have hle : n ≤ 3 * φ n := le_three_mul_totient_of_primes_le_three n hnpos hsmall
    by_cases hn8 : 8 ≤ n
    · have hmul : 45 * n ≤ 12 * φ n * (n + 4) := by
        calc
          45 * n ≤ 4 * n * (n + 4) := by nlinarith
          _ ≤ 4 * (3 * φ n) * (n + 4) := by
            have hle2 : 4 * n ≤ 4 * (3 * φ n) := by nlinarith
            exact mul_le_mul_right (n + 4) hle2
          _ = 12 * φ n * (n + 4) := by ring
      have h3 : 3 * (15 * n) = 45 * n := by ring
      have h3' : 3 * (4 * φ n * (n + 4)) = 12 * φ n * (n + 4) := by ring
      rw [← h3, ← h3'] at hmul
      exact Nat.le_of_mul_le_mul_left hmul (by norm_num : 0 < 3)
    · interval_cases n <;> first | omega | decide

end Commons.NumberTheory.Totient
