import Mathlib

open scoped BigOperators

set_option autoImplicit false

namespace Submission.Vdw

/-- The number of distinct prime divisors of `n`. -/
def omega (n : ℕ) : ℕ :=
  (Nat.primeFactors n).card

/-- The set of prime factors of `0` is empty. -/
lemma primeFactors_zero : Nat.primeFactors 0 = ∅ := by
  ext p
  simp

/-- The set of prime factors of `1` is empty. -/
lemma primeFactors_one : Nat.primeFactors 1 = ∅ := by
  ext p
  simp

/-- `omega 0 = 0`. -/
@[simp] lemma omega_zero : omega 0 = 0 := by
  simp [omega]

/-- `omega 1 = 0`. -/
@[simp] lemma omega_one : omega 1 = 0 := by
  simp [omega]

/-- The prime factors of a product lie in the union of the prime factors of
the factors: `p | a*b` with `p` prime implies `p | a` or `p | b`. -/
lemma primeFactors_mul_subset (a b : ℕ) :
    Nat.primeFactors (a * b) ⊆ Nat.primeFactors a ∪ Nat.primeFactors b := by
  intro p hp
  rcases (Nat.mem_primeFactors.mp hp) with ⟨pp, hdvd, hab0⟩
  have ha0 : a ≠ 0 := by
    intro ha0
    exact hab0 (by simp [ha0])
  have hb0 : b ≠ 0 := by
    intro hb0
    exact hab0 (by simp [hb0])
  have hdis : p ∣ a ∨ p ∣ b := pp.dvd_mul.mp hdvd
  rcases hdis with hpa | hpb
  · rw [Finset.mem_union]
    left
    exact Nat.mem_primeFactors.mpr ⟨pp, hpa, ha0⟩
  · rw [Finset.mem_union]
    right
    exact Nat.mem_primeFactors.mpr ⟨pp, hpb, hb0⟩

/-- `omega` is subadditive (without any coprimality hypothesis). -/
lemma omega_mul_le (a b : ℕ) : omega (a * b) ≤ omega a + omega b := by
  unfold omega
  have hsub : Nat.primeFactors (a * b) ⊆ Nat.primeFactors a ∪ Nat.primeFactors b :=
    primeFactors_mul_subset a b
  calc
    (Nat.primeFactors (a * b)).card ≤ (Nat.primeFactors a ∪ Nat.primeFactors b).card :=
      Finset.card_le_card hsub
    _ ≤ (Nat.primeFactors a).card + (Nat.primeFactors b).card := by
      simpa using (Finset.card_union_le (Nat.primeFactors a) (Nat.primeFactors b))

/-- A prime divides `n^k` (`k ≥ 1`) iff it divides `n`; so the prime factor
sets agree. -/
lemma primeFactors_pow_eq (n k : ℕ) (hk : 1 ≤ k) :
    Nat.primeFactors (n ^ k) = Nat.primeFactors n := by
  ext p
  constructor
  · intro hp
    rcases (Nat.mem_primeFactors.mp hp) with ⟨pp, hdvd, hpk0⟩
    have hn0 : n ≠ 0 := by
      intro hn0
      apply hpk0
      rw [hn0]
      exact zero_pow (by omega : k ≠ 0)
    exact Nat.mem_primeFactors.mpr ⟨pp, pp.dvd_of_dvd_pow hdvd, hn0⟩
  · intro hp
    rcases (Nat.mem_primeFactors.mp hp) with ⟨pp, hdvd, hn0⟩
    have hnk0 : n ^ k ≠ 0 := pow_ne_zero _ hn0
    exact Nat.mem_primeFactors.mpr
      ⟨pp, dvd_pow hdvd (by omega : k ≠ 0), hnk0⟩

/-- `omega` is invariant under raising to a positive power. -/
lemma omega_pow_eq (n k : ℕ) (hk : 1 ≤ k) : omega (n ^ k) = omega n := by
  unfold omega
  exact congrArg Finset.card (primeFactors_pow_eq n k hk)

/-- The `ω` of `a²·b³` is at most `ω a + ω b`. -/
lemma omega_sq_mul_cube_le (a b : ℕ) : omega (a ^ 2 * b ^ 3) ≤ omega a + omega b := by
  calc
    omega (a ^ 2 * b ^ 3) ≤ omega (a ^ 2) + omega (b ^ 3) := omega_mul_le (a ^ 2) (b ^ 3)
    _ = omega a + omega b := by rw [omega_pow_eq a 2 (by norm_num), omega_pow_eq b 3 (by norm_num)]

end Submission.Vdw
