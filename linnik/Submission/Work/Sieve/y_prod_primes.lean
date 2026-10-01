import Mathlib

open scoped BigOperators

namespace Work.Sieve

lemma y_prod_primes (y : ℕ → ℝ)
    (hy_mul : ∀ m n : ℕ, Squarefree m → Squarefree n → Nat.Coprime m n →
      y (m * n) = y m * y n)
    (t : Finset ℕ) (ht : ∀ p ∈ t, Nat.Prime p) (hne : t.Nonempty) :
    Squarefree (∏ p ∈ t, p) ∧ y (∏ p ∈ t, p) = ∏ p ∈ t, y p := by
  classical
  -- A product of distinct primes is squarefree.
  have hsf : ∀ (s : Finset ℕ), (∀ p ∈ s, Nat.Prime p) → Squarefree (∏ p ∈ s, p) := by
    intro s hs
    exact Finset.squarefree_prod_of_pairwise_isCoprime
      (fun p hp q hq hpq => Nat.coprime_iff_isRelPrime.mp
        ((Nat.coprime_primes (hs p hp) (hs q hq)).mpr hpq))
      (fun p hp => (hs p hp).prime.squarefree)
  -- Multiplicativity over a nonempty family of primes, by induction on the finset.
  have hmul : ∀ (s : Finset ℕ), s.Nonempty → (∀ p ∈ s, Nat.Prime p) →
      y (∏ p ∈ s, p) = ∏ p ∈ s, y p := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro h _; exact absurd h Finset.not_nonempty_empty
    | insert a s has ih =>
      intro _ hs
      rw [Finset.prod_insert has, Finset.prod_insert has]
      have hpa : Nat.Prime a := hs a (Finset.mem_insert_self a s)
      have hs' : ∀ p ∈ s, Nat.Prime p := fun p hp => hs p (Finset.mem_insert_of_mem hp)
      by_cases hse : s.Nonempty
      · have hcop : Nat.Coprime a (∏ p ∈ s, p) :=
          Nat.Coprime.prod_right (fun p hp =>
            (Nat.coprime_primes hpa (hs' p hp)).mpr (fun h => has (h ▸ hp)))
        rw [hy_mul a (∏ p ∈ s, p) hpa.prime.squarefree (hsf s hs') hcop, ih hse hs']
      · have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hse
        rw [hempty]; simp
  exact ⟨hsf t ht, hmul t hne ht⟩

end Work.Sieve
