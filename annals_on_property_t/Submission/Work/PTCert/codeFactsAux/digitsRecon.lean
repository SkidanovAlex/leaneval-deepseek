import Mathlib
import Submission.Work.PTCert.Interfaces

/-!
# Digit reconstruction and the `pdig`/`sbit` bridges

Shared helpers for `Work.PTCert.codeFacts` (and the auxiliary pieces it delegates).

* `selfDigits`: a natural number `n < b ^ k` is the sum `∑ i < k, (n / b^i % b) * b^i`
  of its base-`b` digits;
* `pdig_eq_div`, `sbit_eq_div`: the code digits `pdig`, `sbit` are the quotient-remainder
  digits `pc / 8^i % 8` resp. `sc / 2^i % 2`.
-/

namespace Work.PTCert

open Submission.PTCert

/-- **Digit reconstruction.**  A natural number below `b ^ k` is the sum of its `k` base-`b`
digits: `n = ∑_{i<k} (n / b^i % b) * b^i`. -/
theorem selfDigits {b : ℕ} (hb : 2 ≤ b) (n k : ℕ) (hn : n < b ^ k) :
    n = ∑ i ∈ Finset.range k, (n / b ^ i % b) * b ^ i := by
  have hbpos : 0 < b := by omega
  induction k generalizing n with
  | zero =>
    simp only [pow_zero] at hn
    simp only [Finset.range_zero, Finset.sum_empty]
    omega
  | succ k ih =>
    rw [pow_succ] at hn
    set d : ℕ := n / b ^ k with hd
    set m : ℕ := n % b ^ k with hm
    have hm_lt : m < b ^ k := Nat.mod_lt _ (pow_pos hbpos k)
    have hd_lt : d < b := by
      rw [hd]
      exact Nat.div_lt_of_lt_mul hn
    have hdecomp : n = m + b ^ k * d := by
      have h := Nat.div_add_mod n (b ^ k)
      rw [← hd, ← hm] at h
      omega
    have hterm : ∀ i ∈ Finset.range k, (n / b ^ i % b) * b ^ i = (m / b ^ i % b) * b ^ i := by
      intro i hi
      have hik : i < k := Finset.mem_range.mp hi
      have hle : i ≤ k := le_of_lt hik
      have hpow : b ^ k = b ^ i * b ^ (k - i) := by
        rw [← pow_add, Nat.add_sub_cancel' hle]
      have hn' : n = m + b ^ i * (b ^ (k - i) * d) := by
        rw [hdecomp, hpow]; ring
      have hdiv : n / b ^ i = m / b ^ i + b ^ (k - i) * d := by
        rw [hn', Nat.add_mul_div_left _ _ (pow_pos hbpos i)]
      have hb_dvd : b ∣ b ^ (k - i) * d := by
        have hpos : 0 < k - i := by omega
        obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k - i ≠ 0)
        rw [hj, pow_succ]
        exact ⟨b ^ j * d, by ring⟩
      congr 1
      rw [hdiv]
      simp [Nat.add_mod, Nat.mod_eq_zero_of_dvd hb_dvd]
    rw [Finset.sum_range_succ, Finset.sum_congr rfl hterm, ← ih m hm_lt]
    have hk : (n / b ^ k) % b = d := by
      rw [hd, Nat.mod_eq_of_lt hd_lt]
    rw [hk, hdecomp]
    ring

/-- `pdig` reads the base-`8` digits: `pdig pc i = pc / 8^i % 8`. -/
theorem pdig_eq_div (pc i : ℕ) : pdig pc i = pc / 8 ^ i % 8 := by
  unfold pdig
  rw [Nat.shiftRight_eq_div_pow,
    show (2 : ℕ) ^ (3 * i) = 8 ^ i from by rw [Nat.pow_mul]]

/-- `sbit` reads the binary digits: `sbit sc i = sc / 2^i % 2`. -/
theorem sbit_eq_div (sc i : ℕ) : sbit sc i = sc / 2 ^ i % 2 := by
  unfold sbit
  rw [Nat.shiftRight_eq_div_pow]

end Work.PTCert
