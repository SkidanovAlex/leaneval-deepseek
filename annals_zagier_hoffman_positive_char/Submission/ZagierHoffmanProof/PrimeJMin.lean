import Submission.ZagierHoffmanProof.PrimeGreedy

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Polynomial RatFunc
open scoped BigOperators WithZero
open WithZero

/-!
# The least admissible shift is the greedy fill

For a finite field `F` whose cardinality `q` is prime, the least good shift `jMin F k`
(Thakur's `j_min(k)`) is exactly the greedy fill `greedy q (k-1)` of the capacities
`capp q (k-1) i = q - 1 - (k-1) / q^i % q`.
-/

namespace ZagierHoffmanPositiveChar

section DsumDvd

/-- The digit sum of a multiple of `p - 1` is again a multiple of `p - 1`. -/
lemma dsum_dvd_of_dvd {p j : ℕ} (hp : 1 < p) (h : (p - 1) ∣ j) : (p - 1) ∣ dsum p j := by
  have h1 := dsum_modEq hp j
  rw [Nat.ModEq] at h1
  rw [Nat.dvd_iff_mod_eq_zero] at h ⊢
  rw [← h1]
  exact h

/-- A positive multiple of `p - 1` has digit sum at least `p - 1`. -/
lemma le_dsum_of_dvd {p j : ℕ} (hp : 2 ≤ p) (h : (p - 1) ∣ j) (hj : 1 ≤ j) :
    p - 1 ≤ dsum p j := by
  have hd := dsum_dvd_of_dvd (p := p) (by omega : 1 < p) h
  have h1 : 1 ≤ dsum p j := dsum_pos (by omega : 1 < p) hj
  rcases hd with ⟨c, hc⟩
  rcases Nat.eq_zero_or_pos c with h0 | h0
  · rw [h0, mul_zero] at hc
    omega
  · have hle : p - 1 ≤ (p - 1) * c := by
      simpa using Nat.mul_le_mul_left (p - 1) h0
    omega

end DsumDvd

section JMinGreedy

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- A finite field has at least two elements. -/
lemma two_le_card : 2 ≤ Nat.card F := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  have h := Fintype.one_lt_card (α := F)
  rwa [Fintype.card_eq_nat_card] at h

/-- The capacities `capp p n i` encode the digitwise no-carry condition. -/
lemma noCarry_iff_capp {p n j : ℕ} (hp : 2 ≤ p) :
    (∀ i, j / p ^ i % p ≤ capp p n i) ↔ noCarry p j n := by
  unfold noCarry capp
  have hp0 : 0 < p := by omega
  constructor
  · intro h i
    have h1 : n / p ^ i % p ≤ p - 1 := by
      have := Nat.mod_lt (n / p ^ i) hp0; omega
    have h2 := h i
    omega
  · intro h i
    have h1 : n / p ^ i % p ≤ p - 1 := by
      have := Nat.mod_lt (n / p ^ i) hp0; omega
    have h2 := h i
    omega

/-- **The least good shift is the greedy fill.** -/
theorem jMin_eq_greedy (hp : (Nat.card F).Prime) (k : ℕ+) :
    jMin F k = greedy (Nat.card F) (two_le_card F) ((k : ℕ) - 1) := by
  have hq2 : 2 ≤ Nat.card F := two_le_card F
  have hk1 : 1 ≤ (k : ℕ) := k.pos
  have hiff := isGoodJ_iff_noCarry F hp (k : ℕ)
  refine le_antisymm ?_ ?_
  · -- the greedy fill is a good shift, so it is at least `jMin`
    have hgood : IsGoodJ F (k : ℕ) (greedy (Nat.card F) hq2 ((k : ℕ) - 1)) := by
      rw [hiff _ hk1]
      refine ⟨greedy_pos hq2 _, greedy_dvd hq2 _, ?_⟩
      rw [← noCarry_iff_capp hq2]
      exact greedy_digit_le hq2 _
    exact jMin_le F hgood
  · -- `jMin` is admissible, so the greedy fill is at most it
    have hj := (hiff _ hk1).mp (jMin_spec F k)
    refine greedy_le hq2 _ _ ?_ ?_
    · rw [noCarry_iff_capp hq2]
      exact hj.2.2
    · exact le_dsum_of_dvd hq2 hj.2.1 hj.1

end JMinGreedy

end ZagierHoffmanPositiveChar
