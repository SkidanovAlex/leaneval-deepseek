import Mathlib
import Submission.Work.PTCert.GlueDefs
import Submission.Work.PTCert.digits.sum_mul_pow_div_mod
import Submission.Work.PTCert.digits.sum_mul_pow_lt_pow

/-!
# `scOf` turns addition in `(ℤ/2)^5` into `Nat.xor` of the sign codes

The sign code `scOf s = ∑ i, (if s i then 1 else 0) · 2^i` reads a `Bool`-vector of length `5` as
the bits of a natural number (`s 0` is the least significant bit).  Since addition in `ZMod 2` is
componentwise XOR of bits, the code of a sum is the bitwise XOR of the codes:

`scOf (zBool (a + b)) = scOf (zBool a) ^^^ scOf (zBool b)`.

The proof is a bit-level argument.  Writing `bitN a j` for the `j`-th bit (`0` for `j ≥ 5`) and
`enc a = ∑_{j<5} bitN a j · 2^j`:

* `enc a = scOf (zBool a)` (unfold both sides);
* `testBit (enc a) j = decide (bitN a j = 1)`: the digits of a positional sum are its summands
  (`Work.PTCert.digits.sum_mul_pow_div_mod`), and above the fifth bit everything is `0`
  (`enc a < 2^5`);
* `bitN (a + b) j = (bitN a j + bitN b j) % 2`, a four-case check in `ZMod 2`;
* two numbers are equal when all their bits agree (`Nat.eq_of_testBit_eq`) and the bit of
  `x ^^^ y` is the XOR of the bits (`Nat.testBit_xor`), which for `0/1`-digits is
  `(u + v) % 2`.
-/

namespace Work.PTCert

open Submission.PTCert

/-! ## Bits of a `ZMod 2`-vector and its binary code -/

/-- The `j`-th bit of a `ZMod 2`-vector, as `0` or `1`; bits outside `Fin 5` vanish. -/
private def bitN (a : Fin 5 → ZMod 2) (j : ℕ) : ℕ :=
  if h : j < 5 then (if a ⟨j, h⟩ = 1 then 1 else 0) else 0

/-- The binary code of a `ZMod 2`-vector. -/
private def enc (a : Fin 5 → ZMod 2) : ℕ :=
  ∑ i : Fin 5, (if a i = 1 then 1 else 0) * 2 ^ (i : ℕ)

private lemma bitN_lt_two (a : Fin 5 → ZMod 2) (j : ℕ) : bitN a j < 2 := by
  unfold bitN
  split_ifs <;> omega

private lemma bitN_of_lt (a : Fin 5 → ZMod 2) {j : ℕ} (h : j < 5) :
    bitN a j = (if a ⟨j, h⟩ = 1 then 1 else 0) := by
  simp [bitN, h]

private lemma bitN_of_ge (a : Fin 5 → ZMod 2) {j : ℕ} (h : ¬ j < 5) : bitN a j = 0 := by
  simp [bitN, h]

private lemma zmod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  have h : x.val = 0 ∨ x.val = 1 := by
    have h2 : x.val < 2 := ZMod.val_lt x
    omega
  rcases h with h | h
  · exact Or.inl (ZMod.val_injective 2 (by rw [h, ZMod.val_zero]))
  · exact Or.inr (ZMod.val_injective 2 (by rw [h, ZMod.val_one 2]))

private lemma enc_eq_range (a : Fin 5 → ZMod 2) :
    enc a = ∑ j ∈ Finset.range 5, bitN a j * 2 ^ j := by
  rw [enc]
  rw [show (∑ i : Fin 5, (if a i = 1 then 1 else 0) * 2 ^ (i : ℕ))
      = ∑ i : Fin 5, bitN a i * 2 ^ (i : ℕ) from
    Finset.sum_congr rfl (fun i _ => by rw [bitN_of_lt a i.isLt])]
  exact Fin.sum_univ_eq_sum_range (fun j => bitN a j * 2 ^ j) 5

private lemma enc_lt (a : Fin 5 → ZMod 2) : enc a < 2 ^ 5 := by
  rw [enc_eq_range]
  exact digits.sum_mul_pow_lt_pow (b := 2) (by norm_num) (bitN a) 5 (fun j _ => bitN_lt_two a j)

/-- The bits of the code `enc a` are the bits of `a`. -/
private lemma testBit_enc (a : Fin 5 → ZMod 2) (j : ℕ) :
    (enc a).testBit j = decide (bitN a j = 1) := by
  by_cases hj : j < 5
  · rw [Nat.testBit_eq_decide_div_mod_eq]
    have h : enc a / 2 ^ j % 2 = bitN a j := by
      rw [enc_eq_range]
      exact digits.sum_mul_pow_div_mod (b := 2) (by norm_num) (bitN a) 5 j
        (fun i _ => bitN_lt_two a i) hj
    rw [h]
  · have hlt : enc a < 2 ^ j :=
      lt_of_lt_of_le (enc_lt a) (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.testBit_lt_two_pow hlt, bitN_of_ge a hj]
    rfl

/-! ## Addition of the bits -/

/-- In `ZMod 2` the bit of a sum is the XOR of the bits, i.e. their sum modulo `2`. -/
private lemma zmod2_bit_add (x y : ZMod 2) :
    (if x + y = 1 then 1 else 0)
      = ((if x = 1 then 1 else 0) + (if y = 1 then 1 else 0)) % 2 := by
  rcases zmod2_eq_zero_or_one x with rfl | rfl <;>
    rcases zmod2_eq_zero_or_one y with rfl | rfl <;> decide

private lemma bitN_add (a b : Fin 5 → ZMod 2) (j : ℕ) :
    bitN (a + b) j = (bitN a j + bitN b j) % 2 := by
  by_cases hj : j < 5
  · rw [bitN_of_lt (a + b) hj, bitN_of_lt a hj, bitN_of_lt b hj]
    exact zmod2_bit_add _ _
  · rw [bitN_of_ge (a + b) hj, bitN_of_ge a hj, bitN_of_ge b hj]

/-- Two `0/1`-digits `^` to the XOR of their sum modulo `2`. -/
private lemma decide_mod_two_eq_one_xor (u v : ℕ) (hu : u < 2) (hv : v < 2) :
    decide ((u + v) % 2 = 1) = (decide (u = 1) ^^ decide (v = 1)) := by
  have hu' : u = 0 ∨ u = 1 := by omega
  have hv' : v = 0 ∨ v = 1 := by omega
  rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl <;> decide

/-! ## The code of a sign vector is `enc` -/

private lemma scOf_zBool_eq_enc (a : Fin 5 → ZMod 2) : scOf (zBool a) = enc a := by
  simp [Submission.PTCert.scOf, Submission.PTCert.zBool, enc]

/-! ## The main statement -/

theorem scOf_zBool_add (a b : Fin 5 → ZMod 2) :
    Submission.PTCert.scOf (Submission.PTCert.zBool (a + b))
      = Submission.PTCert.scOf (Submission.PTCert.zBool a) ^^^ Submission.PTCert.scOf (Submission.PTCert.zBool b) := by
  rw [scOf_zBool_eq_enc (a + b), scOf_zBool_eq_enc a, scOf_zBool_eq_enc b]
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_xor, testBit_enc, bitN_add]
  exact decide_mod_two_eq_one_xor (bitN a j) (bitN b j) (bitN_lt_two a j) (bitN_lt_two b j)

end Work.PTCert
