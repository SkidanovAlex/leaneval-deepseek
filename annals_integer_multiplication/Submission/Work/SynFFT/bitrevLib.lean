import Mathlib
import Submission.Work.SynFFT.defs

/-!
# Bit-level theory of `bitrev`

`bitrev k n` reverses the low `k` bits of `n`.  This file develops the elementary
binary-digit theory that the facts about `bitrev` rest on:

* `bitsum c L = ∑_{i<L} c i * 2^i` — the number with binary digits `c 0, …, c (L-1)`
  (least significant first);
* `bitsum_lt`, `bitsum_add`, `bitsum_succ`, `bitsum_cons`, `bitsum_mod`, `bitsum_digit` —
  its basic algebra: it is bounded by `2^L`, is additive on shifts of the index set, and
  recovers the individual digits by `% 2^j` / `/ 2^i % 2`;
* `nat_bit_iff` — the `i`-th binary digit of `n` read off from `n % 2^(i+1)`;
* `bitrev_eq_bitsum` — `bitrev` as a `bitsum`;
* `bitrev_bit` — the `i`-th bit of `bitrev k n` is the `(k-1-i)`-th bit of `n`;
* `eq_bitsum_bit` — every `n < 2^k` is reconstructed from its own bits.
-/

set_option autoImplicit false

namespace Work.SynFFT

open scoped BigOperators

/-- `bitsum c L = ∑_{i<L} c i * 2^i`: the number with binary digits `c 0, …, c (L-1)`
(least significant first). -/
def bitsum (c : ℕ → ℕ) (L : ℕ) : ℕ := ∑ i ∈ Finset.range L, c i * 2 ^ i

/-- A sum of digits times powers of two is below `2^L`. -/
lemma bitsum_lt (c : ℕ → ℕ) (hc : ∀ i, c i ≤ 1) (L : ℕ) : bitsum c L < 2 ^ L := by
  induction L with
  | zero => simp [bitsum]
  | succ L ih =>
    unfold bitsum at ih ⊢
    rw [Finset.sum_range_succ]
    have hle : c L * 2 ^ L ≤ 2 ^ L := by
      calc c L * 2 ^ L ≤ 1 * 2 ^ L := by gcongr; exact hc L
        _ = 2 ^ L := one_mul _
    have h2 : (2:ℕ)^L + 2^L = 2^(L+1) := by ring
    omega

/-- Splitting `bitsum` at index `j`. -/
lemma bitsum_add (c : ℕ → ℕ) (j d : ℕ) :
    bitsum c (j + d) = bitsum c j + 2 ^ j * bitsum (fun i => c (i + j)) d := by
  simp only [bitsum, Finset.sum_range_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_add]
  ring_nf

/-- Splitting off the top digit. -/
lemma bitsum_succ (c : ℕ → ℕ) (L : ℕ) :
    bitsum c (L + 1) = bitsum c L + c L * 2 ^ L := by
  simp [bitsum, Finset.sum_range_succ]

/-- Splitting off the bottom digit. -/
lemma bitsum_cons (c : ℕ → ℕ) (L : ℕ) :
    bitsum c (L + 1) = c 0 + 2 * bitsum (fun i => c (i + 1)) L := by
  rw [show L + 1 = 1 + L by omega, bitsum_add]
  simp [bitsum]

/-- The low `j` bits of a `bitsum` are the first `j` digits. -/
lemma bitsum_mod (c : ℕ → ℕ) (hc : ∀ i, c i ≤ 1) {j L : ℕ} (hj : j ≤ L) :
    bitsum c L % 2 ^ j = bitsum c j := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [bitsum_add]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (bitsum_lt c hc j)]

/-- The `i`-th binary digit of a `bitsum` is the `i`-th digit. -/
lemma bitsum_digit (c : ℕ → ℕ) (hc : ∀ i, c i ≤ 1) {i L : ℕ} (hi : i < L) :
    bitsum c L / 2 ^ i % 2 = c i := by
  obtain ⟨d, rfl⟩ : ∃ d, L = (i + 1) + d := ⟨L - (i+1), by omega⟩
  rw [bitsum_add, bitsum_succ]
  set U := bitsum (fun k => c (k + (i + 1))) d
  have hcomb : bitsum c i + c i * 2 ^ i + 2 ^ (i + 1) * U =
      bitsum c i + (c i + 2 * U) * 2 ^ i := by
    rw [pow_succ]; ring
  rw [hcomb]
  rw [Nat.add_mul_div_right]
  · rw [Nat.div_eq_of_lt (bitsum_lt c hc i), Nat.zero_add]
    rw [Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by have := hc i; omega)
  · positivity

/-- The `m`-th binary digit of `n`, computed from `n % 2^(m+1)`. -/
lemma nat_bit_iff (n m : ℕ) :
    n / 2 ^ m % 2 = (if n % 2 ^ (m + 1) ≥ 2 ^ m then 1 else 0) := by
  have hdecomp : n = 2^(m+1) * (n / 2^(m+1)) + n % 2^(m+1) :=
    (Nat.div_add_mod n (2^(m+1))).symm
  have hr : n % 2^(m+1) < 2^(m+1) := Nat.mod_lt _ (by positivity)
  have hr2 : n % 2^(m+1) / 2^m < 2 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    rw [pow_succ'] at hr ⊢
    exact hr
  have key : n / 2^m = n % 2^(m+1) / 2^m + 2 * (n / 2^(m+1)) := by
    conv_lhs => rw [hdecomp]
    rw [show 2^(m+1) * (n / 2^(m+1)) = 2^m * (2 * (n / 2^(m+1))) by rw [pow_succ']; ring]
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by positivity)]
  rw [key]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr2]
  by_cases h : 2^m ≤ n % 2^(m+1)
  · rw [ite_eq_left h]
    exact Nat.div_eq_of_lt_le (k := 1) (by simpa using h)
      (by rw [one_add_one_eq_two, ← pow_succ']; exact hr)
  · rw [ite_eq_right h, Nat.div_eq_of_lt (Nat.lt_of_not_le h)]

/-- `bitrev k n` is the number whose `j`-th binary digit is the `(k-1-j)`-th digit of `n`. -/
lemma bitrev_eq_bitsum (k n : ℕ) :
    bitrev k n = bitsum (fun j => n / 2 ^ (k - 1 - j) % 2) k := by
  rw [bitrev, bitsum]
  conv_rhs => rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range] at hi
  rw [show k - 1 - (k - 1 - i) = i by omega]

/-- The `i`-th bit of `bitrev k n` is the `(k-1-i)`-th bit of `n`. -/
lemma bitrev_bit {k n i : ℕ} (hi : i < k) :
    bitrev k n / 2 ^ i % 2 = n / 2 ^ (k - 1 - i) % 2 := by
  rw [bitrev_eq_bitsum]
  refine bitsum_digit (fun j => n / 2 ^ (k - 1 - j) % 2) (fun j => ?_) hi
  have := Nat.mod_lt (n / 2 ^ (k - 1 - j)) (show 0 < 2 by norm_num)
  omega

/-- Every `n < 2^k` is recovered from its own binary digits. -/
lemma eq_bitsum_bit (k n : ℕ) (hn : n < 2 ^ k) :
    n = bitsum (fun i => n / 2 ^ i % 2) k := by
  revert n
  induction k with
  | zero => intro n hn; simp [bitsum]; omega
  | succ k ih =>
    intro n hn
    have hd : n / 2 < 2 ^ k := by
      rw [Nat.div_lt_iff_lt_mul (by norm_num)]
      rwa [pow_succ] at hn
    have hcongr : (fun i => n / 2 ^ (i + 1) % 2) = (fun i => (n / 2) / 2 ^ i % 2) := by
      funext i
      rw [Nat.div_div_eq_div_mul, show 2 * 2 ^ i = 2 ^ (i + 1) by rw [pow_succ']]
    rw [bitsum_cons, hcongr, ← ih (n / 2) hd]
    simp only [pow_zero, Nat.div_one]
    exact (Nat.mod_add_div n 2).symm

end Work.SynFFT
