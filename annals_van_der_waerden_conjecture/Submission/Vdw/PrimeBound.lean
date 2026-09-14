import Mathlib
import Submission.Vdw.Omega

open scoped BigOperators
open Finset

set_option autoImplicit false

/-!
# Bounded prime-divisor counts from a power bound

Pure number-theoretic input for the Case-III subcase-(ii) bookkeeping (and other
places where one must bound the number of large prime divisors of a small
integer).  The two main facts:

1. `pow_omega_le_of_primeFactors_ge`: if every prime divisor of `z` is at least
   `B` (`1 < B`), then `B ^ omega z ≤ z` (multiplying the distinct prime
   divisors, each ≥ B, against the fact that their product divides `z`).
2. `omega_le_log_mul`: if moreover `z ≤ H ^ K`, then
   `omega z ≤ K * (Nat.log B H + 1)`  (taking `Nat.log B` on both sides of
   `B ^ omega z ≤ z ≤ H ^ K` and using `Nat.log_pow`).

`bigPrimeDivs B z` is the finite set of prime divisors of `z` that are at least
`B`; its cardinality is bounded by the same quantities since it is a subset of
`z.primeFactors`.
-/

namespace Submission.Vdw

/-- The set of prime divisors of `z` that are at least `B`. -/
def bigPrimeDivs (B z : ℕ) : Finset ℕ :=
  (Nat.primeFactors z).filter fun p => B ≤ p

/-- `bigPrimeDivs B z` is contained in `z.primeFactors`. -/
lemma bigPrimeDivs_subset_primeFactors (B z : ℕ) : bigPrimeDivs B z ⊆ Nat.primeFactors z := by
  intro p hp
  exact (Finset.mem_filter.mp hp).1

/-- Every element of `bigPrimeDivs B z` is at least `B`. -/
lemma le_of_mem_bigPrimeDivs {B z p : ℕ} (hp : p ∈ bigPrimeDivs B z) : B ≤ p :=
  (Finset.mem_filter.mp hp).2

/-- Every element of `bigPrimeDivs B z` is a prime divisor of `z`. -/
lemma mem_primeFactors_of_mem_bigPrimeDivs {B z p : ℕ} (hp : p ∈ bigPrimeDivs B z) :
    p ∈ Nat.primeFactors z :=
  bigPrimeDivs_subset_primeFactors B z hp

/-- The cardinality of `bigPrimeDivs B z` is at most `omega z`. -/
lemma bigPrimeDivs_card_le_omega (B z : ℕ) : (bigPrimeDivs B z).card ≤ omega z := by
  unfold bigPrimeDivs omega
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- If every prime divisor of a nonzero `z` is at least `B`, then
`B ^ omega z ≤ z`. -/
lemma pow_omega_le_of_primeFactors_ge {B z : ℕ} (hz : z ≠ 0)
    (hmin : ∀ p ∈ Nat.primeFactors z, B ≤ p) : B ^ omega z ≤ z := by
  have hleprod : (∏ p ∈ Nat.primeFactors z, B) ≤ (∏ p ∈ Nat.primeFactors z, p) := by
    refine Finset.prod_le_prod ?h0 ?h1
    · intro p hp
      exact Nat.zero_le B
    · intro p hp
      exact hmin p hp
  have hprod : (∏ p ∈ Nat.primeFactors z, B) = B ^ omega z := by
    unfold omega
    rw [Finset.prod_const]
  calc
    B ^ omega z = ∏ p ∈ Nat.primeFactors z, B := hprod.symm
    _ ≤ ∏ p ∈ Nat.primeFactors z, p := hleprod
    _ ≤ z := Nat.le_of_dvd (Nat.pos_of_ne_zero hz) (Nat.prod_primeFactors_dvd z)

/-- If every prime divisor of `z` is at least `B` and `z ≤ H ^ K`, then
`omega z ≤ K * (Nat.log B H + 1)`. -/
theorem omega_le_log_mul {B z K H : ℕ} (hB : 1 < B) (hz : z ≠ 0)
    (hmin : ∀ p ∈ Nat.primeFactors z, B ≤ p) (hle : z ≤ H ^ K) :
    omega z ≤ K * (Nat.log B H + 1) := by
  -- `H ≤ B ^ (log B H + 1)`, hence `H ^ K ≤ B ^ (K * (log B H + 1))`
  have hHpow : H ≤ B ^ (Nat.log B H + 1) := by
    have hlt := Nat.lt_pow_succ_log_self hB H
    exact le_of_lt (by simpa using hlt)
  have h1 : B ^ omega z ≤ H ^ K :=
    le_trans (pow_omega_le_of_primeFactors_ge hz hmin) hle
  have h1' : H ^ K ≤ B ^ (K * (Nat.log B H + 1)) := by
    calc
      H ^ K ≤ (B ^ (Nat.log B H + 1)) ^ K := Nat.pow_le_pow_left hHpow K
      _ = B ^ ((Nat.log B H + 1) * K) := by rw [pow_mul]
      _ = B ^ (K * (Nat.log B H + 1)) := by rw [Nat.mul_comm]
  calc
    omega z = Nat.log B (B ^ omega z) := (Nat.log_pow hB (omega z)).symm
    _ ≤ Nat.log B (H ^ K) := Nat.log_mono_right h1
    _ ≤ Nat.log B (B ^ (K * (Nat.log B H + 1))) := Nat.log_mono_right h1'
    _ = K * (Nat.log B H + 1) := Nat.log_pow hB (K * (Nat.log B H + 1))

/-- If `z` is nonzero, has all its prime divisors at least `B`, and `z ≤ H ^ K`,
then the number of its prime divisors of size at least `B` is at most
`K * (Nat.log B H + 1)`. -/
theorem bigPrimeDivs_card_le_log_mul {B z K H : ℕ} (hB : 1 < B) (hz : z ≠ 0)
    (hmin : ∀ p ∈ Nat.primeFactors z, B ≤ p) (hle : z ≤ H ^ K) :
    (bigPrimeDivs B z).card ≤ K * (Nat.log B H + 1) := by
  exact le_trans (bigPrimeDivs_card_le_omega B z) (omega_le_log_mul hB hz hmin hle)

/-- A direct upper bound: if `z` is nonzero and `z ≤ H ^ K`, then every prime
divisor of `z` is at most `H ^ K`, hence ... (trivial divisibility bound). -/
lemma primeFactor_le_self {z p : ℕ} (hp : p ∈ Nat.primeFactors z) : p ≤ z :=
  Nat.le_of_mem_primeFactors hp

end Submission.Vdw
