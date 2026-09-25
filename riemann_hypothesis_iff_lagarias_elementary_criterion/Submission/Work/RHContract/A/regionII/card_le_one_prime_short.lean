import Mathlib

namespace Work.RHContract.A.regionII

/-- Two distinct primes that are both `≥ 3` differ by at least `2`:
primes greater than `2` are odd, so they have the same parity. -/
lemma two_le_sub_of_prime {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hp3 : 3 ≤ p) (hq3 : 3 ≤ q) (hpq : p < q) : 2 ≤ q - p := by
  have hpodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have hqodd : q % 2 = 1 := by
    rcases hq.eq_two_or_odd with h | h
    · omega
    · exact h
  omega

/-- A finite set of primes `≥ 3` lying strictly inside an interval of real length `< 2`
has at most one element: two distinct such primes are at least `2` apart. -/
theorem card_le_one_prime_short {A : Finset ℕ} {a b : ℝ}
    (hA : ∀ p ∈ A, Nat.Prime p) (h3 : ∀ p ∈ A, 3 ≤ p)
    (hgt : ∀ p ∈ A, a < (p:ℝ)) (hlt : ∀ p ∈ A, (p:ℝ) < b) (hba : b - a < 2) :
    A.card ≤ 1 := by
  rw [Finset.card_le_one]
  intro p hp q hq
  by_contra hne
  have hpodd : p % 2 = 1 := by
    rcases (hA p hp).eq_two_or_odd with h | h
    · exact absurd h (by have := h3 p hp; omega)
    · exact h
  have hqodd : q % 2 = 1 := by
    rcases (hA q hq).eq_two_or_odd with h | h
    · exact absurd h (by have := h3 q hq; omega)
    · exact h
  rcases lt_trichotomy p q with hpq | hpq | hpq
  · have hgap : p + 2 ≤ q := by omega
    have hgap' : (p:ℝ) + 2 ≤ (q:ℝ) := by exact_mod_cast hgap
    linarith [hgt p hp, hlt q hq, hba]
  · exact hne hpq
  · have hgap : q + 2 ≤ p := by omega
    have hgap' : (q:ℝ) + 2 ≤ (p:ℝ) := by exact_mod_cast hgap
    linarith [hgt q hq, hlt p hp, hba]

end Work.RHContract.A.regionII
