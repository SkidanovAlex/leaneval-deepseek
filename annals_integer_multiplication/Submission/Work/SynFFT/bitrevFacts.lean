import Mathlib
import Submission.Work.SynFFT.defs
import Submission.Work.SynFFT.bitrevLib
import Submission.Work.SynFFT.bitrevMod
import Submission.Work.SynFFT.bitrevRec

/-!
# Facts about bit reversal

`bitrev k n` reverses the low `k` bits of `n`.  We prove the elementary facts used by the
synthetic FFT development:

* `bitrev k n < 2^k`;
* `bitrev k` is an involution of `{0, …, 2^k - 1}`, hence injective there;
* the recursion `bitrev (k+1) (2n) = bitrev k n`, `bitrev (k+1) (2n+1) = 2^k + bitrev k n`;
* the low `j` bits of `bitrev k p` are given by the first `j` reversed digits of `p`.
-/

set_option autoImplicit false

namespace Work.SynFFT

open scoped BigOperators

/-- The bit-reversal sends `{0, …, 2^k-1}` into itself. -/
lemma bitrev_lt (k n : ℕ) : bitrev k n < 2 ^ k := by
  rw [bitrev_eq_bitsum]
  refine bitsum_lt _ (fun j => ?_) k
  have := Nat.mod_lt (n / 2 ^ (k - 1 - j)) (show 0 < 2 by norm_num)
  omega

/-- Bit reversal is an involution on numbers below `2^k`. -/
lemma bitrev_invol (k n : ℕ) (hn : n < 2 ^ k) : bitrev k (bitrev k n) = n := by
  rcases k with _ | k
  · simp only [pow_zero] at hn
    have hn0 : n = 0 := by omega
    rw [hn0]
    simp [bitrev]
  · rw [bitrev_eq_bitsum]
    conv_rhs => rw [eq_bitsum_bit (k + 1) n hn]
    simp only [bitsum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_range] at hj
    rw [show (k + 1) - 1 - j = k - j by omega]
    rw [bitrev_bit (k := k + 1) (n := n) (i := k - j) (by omega)]
    rw [show (k + 1) - 1 - (k - j) = j by omega]

/-- Bit reversal is injective on numbers below `2^k`. -/
lemma bitrev_inj (k n m : ℕ) (hn : n < 2 ^ k) (hm : m < 2 ^ k)
    (h : bitrev k n = bitrev k m) : n = m := by
  rw [← bitrev_invol k n hn, h, bitrev_invol k m hm]

theorem bitrevFacts :
    (∀ k n : ℕ, bitrev k n < 2 ^ k) ∧
    (∀ (k n : ℕ), n < 2 ^ k → bitrev k (bitrev k n) = n) ∧
    (∀ (k n m : ℕ), n < 2 ^ k → m < 2 ^ k → bitrev k n = bitrev k m → n = m) ∧
    (∀ (k n : ℕ), bitrev (k + 1) (2 * n) = bitrev k n) ∧
    (∀ (k n : ℕ), bitrev (k + 1) (2 * n + 1) = 2 ^ k + bitrev k n) ∧
    (∀ (k j p : ℕ), j ≤ k → p < 2 ^ k →
      (∑ i ∈ Finset.range j,
          (if p % 2 ^ (k - i) ≥ 2 ^ (k - i - 1) then 1 else 0) * 2 ^ i) = bitrev k p % 2 ^ j) := by
  exact ⟨bitrev_lt, bitrev_invol, bitrev_inj, bitrevRec.1, bitrevRec.2, bitrevMod⟩

end Work.SynFFT
