import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Real.Basic

namespace Commons.NumberTheory.ArithmeticFunction

/-- If `g` is multiplicative on coprime arguments with `g 1 = 1`, then its value on a product of
pairwise coprime natural numbers is the product of its values. -/
private lemma prod_id_g_eq_prod_g (g : ℕ → ℝ)
    (hgmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n) (g1 : g 1 = 1) :
    ∀ s : Finset ℕ, (∀ p ∈ s, ∀ q ∈ s, p ≠ q → Nat.Coprime p q) →
      g (∏ p ∈ s, p) = ∏ p ∈ s, g p := by
  intro s
  induction s using Finset.induction_on with
  | empty => intro _; simp [g1]
  | insert a t ha ih =>
    intro hpair
    have hpair_t : ∀ p ∈ t, ∀ q ∈ t, p ≠ q → Nat.Coprime p q :=
      fun p hp q hq hpq =>
        hpair p (Finset.mem_insert_of_mem hp) q (Finset.mem_insert_of_mem hq) hpq
    have hcop : Nat.Coprime a (∏ p ∈ t, p) := by
      rw [Nat.coprime_prod_right_iff]
      intro p hp
      exact hpair a (Finset.mem_insert_self a t) p (Finset.mem_insert_of_mem hp)
        (fun h => ha (h ▸ hp))
    have h1 : g (∏ p ∈ insert a t, p) = g a * g (∏ p ∈ t, p) := by
      rw [Finset.prod_insert ha, hgmul a _ hcop]
    have h2 : ∏ p ∈ insert a t, g p = g a * ∏ p ∈ t, g p := by
      rw [Finset.prod_insert ha]
    rw [h1, h2, ih hpair_t]

theorem g_eq_prod_primeFactors (g : ℕ → ℝ)
    (hgmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n) (g1 : g 1 = 1)
    {n : ℕ} (hn : Squarefree n) :
    g n = ∏ p ∈ n.primeFactors, g p := by
  have hpair : ∀ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors, p ≠ q → Nat.Coprime p q :=
    fun p hp q hq hpq =>
      (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
        (Nat.prime_of_mem_primeFactors hq)).2 hpq
  have h := prod_id_g_eq_prod_g g hgmul g1 n.primeFactors hpair
  rw [Nat.prod_primeFactors_of_squarefree hn] at h
  exact h

end Commons.NumberTheory.ArithmeticFunction