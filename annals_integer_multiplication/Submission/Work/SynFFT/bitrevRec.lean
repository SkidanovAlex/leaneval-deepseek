import Mathlib
import Submission.Work.SynFFT.defs

/-!
# The recursion satisfied by bit reversal

`bitrev k n = ∑_{i<k} (n / 2^i % 2) * 2^(k-1-i)` reverses the low `k` bits of `n`.
Appending one bit to `n` on the *left* (i.e. reading `n` as the low bits and zero- or
one-padding the top bit) shifts the reversal by one position:

* `bitrev (k+1) (2*n)     = bitrev k n`      (the new low bit `0` becomes the top bit);
* `bitrev (k+1) (2*n + 1) = 2^k + bitrev k n` (the new low bit `1` becomes the top bit `2^k`).

These are the recursions that let the bit-reversal permutation of length `2^k` be built
from the one of length `2^(k-1)`, and they are collected as `bitrevRec`.
-/

set_option autoImplicit false

namespace Work.SynFFT

open scoped BigOperators

/-- `2 * n / 2 ^ (i+1) = n / 2 ^ i`. -/
private lemma two_mul_div_two_pow_succ (n i : ℕ) : 2 * n / 2 ^ (i + 1) = n / 2 ^ i := by
  rw [pow_succ']
  exact Nat.mul_div_mul_left n (2 ^ i) (by norm_num)

/-- `(2 * n + 1) / 2 ^ (i+1) = n / 2 ^ i`: the low bit of an odd number is discarded. -/
private lemma two_mul_add_one_div_two_pow_succ (n i : ℕ) :
    (2 * n + 1) / 2 ^ (i + 1) = n / 2 ^ i := by
  rw [pow_succ', ← Nat.div_div_eq_div_mul]
  rw [show (2 * n + 1) / 2 = n by omega]

/-- Shifting in a low `0` bit: the reversal of `2 * n` on `k + 1` bits is that of `n` on `k`. -/
lemma bitrev_succ_two_mul (k n : ℕ) : bitrev (k + 1) (2 * n) = bitrev k n := by
  simp only [bitrev]
  rw [Finset.sum_range_succ']
  have h0 : (2 * n) / 2 ^ 0 % 2 * 2 ^ (k + 1 - 1 - 0) = 0 := by simp [Nat.mul_mod_right]
  rw [h0, add_zero]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range] at hi
  rw [two_mul_div_two_pow_succ, show k + 1 - 1 - (i + 1) = k - 1 - i by omega]

/-- Shifting in a low `1` bit: the reversal of `2 * n + 1` on `k + 1` bits is `2^k` plus that
of `n` on `k` bits (the new bit becomes the top one). -/
lemma bitrev_succ_two_mul_add_one (k n : ℕ) :
    bitrev (k + 1) (2 * n + 1) = 2 ^ k + bitrev k n := by
  simp only [bitrev]
  rw [Finset.sum_range_succ']
  have h0 : (2 * n + 1) / 2 ^ 0 % 2 * 2 ^ (k + 1 - 1 - 0) = 2 ^ k := by simp
  rw [h0]
  have hsum : (∑ i ∈ Finset.range k,
        (2 * n + 1) / 2 ^ (i + 1) % 2 * 2 ^ (k + 1 - 1 - (i + 1))) = bitrev k n := by
    simp only [bitrev]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_range] at hi
    rw [two_mul_add_one_div_two_pow_succ,
      show k + 1 - 1 - (i + 1) = k - 1 - i by omega]
  rw [hsum, Nat.add_comm]
  rfl

theorem bitrevRec :
    (∀ k n : ℕ, bitrev (k + 1) (2 * n) = bitrev k n) ∧
    (∀ k n : ℕ, bitrev (k + 1) (2 * n + 1) = 2 ^ k + bitrev k n) :=
  ⟨bitrev_succ_two_mul, bitrev_succ_two_mul_add_one⟩

end Work.SynFFT
