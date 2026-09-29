import Mathlib
import Submission.Work.IntLib.Defs
import Submission.Work.IntLib.Basic
import Submission.Work.IntLib.Raw
import Submission.Work.IntLib.ofBitsAPI
import Submission.Work.IntLib.ofBits_bits
import Submission.Work.IntLib.encodeNatBridge
import Submission.Work.Kernel.Raw

/-!
# Shared layer for the `size` / `clog 2` / `pow2` integer words

These three `UnOp`s of `HvdH.IntLib` are implemented on top of one common low-level device:

* a **unary counter region** on a scratch stack `k`: `u` copies of the token glyph `gTok` above a
  frame marker `gA`/`gB`/`gC` (which are `Glyph.mk _`, hence never part of a `Val.enc`), written
  `toks u ++ gA :: below`;
* a **bit region** on stack 3: a list of `Glyph.bit _` above a frame marker, representing the binary
  expansion of a natural number, either least-significant-first or most-significant-first.

The plan of each word:

| word | pipeline |
|------|----------|
| `size`   | pop sign, count the bit glyphs into a unary counter, halve the counter to binary bits (stack 3), emit `pos :: bits ++ [iend]` |
| `clog 2` | pop sign, test `a = 0`, decrement the bit string of `\|a\|` to `\|a\|-1`, then run `size` |
| `pow2`   | pop sign, convert the bit string of `k` into a unary counter (MSB-first doubling), emit `pos :: k·false ++ [true, iend]` |

The pure arithmetic facts used by the pipelines live here as well.
-/

set_option autoImplicit false

namespace Work.IntLib
namespace Size

open HvdH

/-! ## Glyphs, tokens, regions -/

/-- The unary-counter token glyph. -/
abbrev gTok : Glyph := .mk 0
/-- Frame marker of the unary-counter region (stack 1). -/
abbrev gA : Glyph := .mk 1
/-- Frame marker of the halving scratch region (stack 2). -/
abbrev gB : Glyph := .mk 2
/-- Frame marker of the bit region (stack 3). -/
abbrev gC : Glyph := .mk 3

/-- `toks u` is `u` copies of the counter token. -/
def toks (u : ℕ) : List Glyph := List.replicate u gTok

@[simp] theorem toks_zero : toks 0 = [] := rfl

theorem toks_succ (u : ℕ) : toks (u + 1) = gTok :: toks u := by
  simp [toks, List.replicate_succ]

@[simp] theorem toks_length (u : ℕ) : (toks u).length = u := by simp [toks, List.length_replicate]

theorem toks_add (u v : ℕ) : toks (u + v) = toks u ++ toks v := by
  unfold toks
  rw [List.replicate_add]

theorem toks_headD (u : ℕ) (M : Glyph) (l : List Glyph) :
    (toks u ++ M :: l).headD .eos = (if u = 0 then M else gTok) := by
  cases u with
  | zero => simp [toks]
  | succ u => simp [toks_succ]

theorem toks_tail (u : ℕ) (M : Glyph) (l : List Glyph) (hu : 1 ≤ u) :
    (toks u ++ M :: l).tail = toks (u - 1) ++ M :: l := by
  obtain ⟨v, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : u ≠ 0)
  simp [toks_succ]

/-- `toks u ++ M :: l` is `M :: l` when `u = 0`. -/
theorem toks_zero_append (M : Glyph) (l : List Glyph) : toks 0 ++ M :: l = M :: l := rfl

theorem toks_headD_zero (M : Glyph) (l : List Glyph) : (toks 0 ++ M :: l).headD .eos = M := rfl

/-- `q` tokens followed by a token and `l` is `q+1` tokens followed by `l`. -/
theorem toks_cons_append (q : ℕ) (l : List Glyph) : toks q ++ (gTok :: l) = toks (q + 1) ++ l := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [show toks (q + 1) = gTok :: toks q from toks_succ q, List.cons_append, ih,
      show toks (q + 1 + 1) = gTok :: toks (q + 1) from toks_succ (q + 1), List.cons_append]

theorem toks_headD_of_pos {u : ℕ} (hu : 1 ≤ u) (M : Glyph) (l : List Glyph) :
    (toks u ++ M :: l).headD .eos = gTok := by
  cases u with
  | zero => omega
  | succ v => simp [toks_succ]

/-! ## Distinctness of the markers -/

theorem gTok_ne_gA : gTok ≠ gA := by decide
theorem gTok_ne_gB : gTok ≠ gB := by decide
theorem gTok_ne_gC : gTok ≠ gC := by decide
theorem gA_ne_gB : gA ≠ gB := by decide
theorem gA_ne_gC : gA ≠ gC := by decide
theorem gB_ne_gC : gB ≠ gC := by decide
theorem gTok_ne_eos : gTok ≠ Glyph.eos := by decide
theorem gA_ne_eos : gA ≠ Glyph.eos := by decide
theorem gB_ne_eos : gB ≠ Glyph.eos := by decide
theorem gC_ne_eos : gC ≠ Glyph.eos := by decide
theorem gTok_ne_iend : gTok ≠ Glyph.iend := by decide
theorem gA_ne_iend : gA ≠ Glyph.iend := by decide
theorem gB_ne_iend : gB ≠ Glyph.iend := by decide
theorem gC_ne_iend : gC ≠ Glyph.iend := by decide
theorem gA_ne_pos : gA ≠ Glyph.pos := by decide
theorem gA_ne_neg : gA ≠ Glyph.neg := by decide
theorem gB_ne_pos : gB ≠ Glyph.pos := by decide
theorem gB_ne_neg : gB ≠ Glyph.neg := by decide
theorem gC_ne_pos : gC ≠ Glyph.pos := by decide
theorem gC_ne_neg : gC ≠ Glyph.neg := by decide
theorem bit_ne_gA (b : Bool) : Glyph.bit b ≠ gA := by cases b <;> decide
theorem bit_ne_gB (b : Bool) : Glyph.bit b ≠ gB := by cases b <;> decide
theorem bit_ne_gC (b : Bool) : Glyph.bit b ≠ gC := by cases b <;> decide
theorem bit_ne_gTok (b : Bool) : Glyph.bit b ≠ gTok := by cases b <;> decide
theorem gTok_ne_bit (b : Bool) : gTok ≠ Glyph.bit b := fun h => bit_ne_gTok b h.symm
theorem iend_ne_gA : Glyph.iend ≠ gA := by decide
theorem iend_ne_gB : Glyph.iend ≠ gB := by decide
theorem iend_ne_gC : Glyph.iend ≠ gC := by decide
theorem iend_ne_gTok : Glyph.iend ≠ gTok := by decide
theorem eos_ne_gTok : Glyph.eos ≠ gTok := by decide
theorem bit_ne_iend (b : Bool) : Glyph.bit b ≠ Glyph.iend := by cases b <;> decide
theorem iend_ne_bit (b : Bool) : Glyph.iend ≠ Glyph.bit b := fun h => bit_ne_iend b h.symm
theorem bit_ne_nil (b : Bool) : Glyph.bit b ≠ Glyph.nil := by cases b <;> decide
theorem bit_ne_cons (b : Bool) : Glyph.bit b ≠ Glyph.cons := by cases b <;> decide
theorem bit_ne_inp (b : Bool) (x y : Option Bool) : Glyph.bit b ≠ Glyph.inp x y := by
  intro h; cases h
theorem bit_ne_eos (b : Bool) : Glyph.bit b ≠ Glyph.eos := by cases b <;> decide
theorem iend_ne_eos : Glyph.iend ≠ Glyph.eos := by decide
theorem pos_ne_gA : Glyph.pos ≠ gA := fun h => gA_ne_pos h.symm
theorem neg_ne_gA : Glyph.neg ≠ gA := fun h => gA_ne_neg h.symm
theorem pos_ne_gTok : Glyph.pos ≠ gTok := by decide
theorem gTok_ne_pos : gTok ≠ Glyph.pos := by decide
theorem gTok_ne_neg : gTok ≠ Glyph.neg := by decide
theorem eos_ne_gA : Glyph.eos ≠ gA := by decide
theorem eos_ne_gC : Glyph.eos ≠ gC := by decide
theorem gA_ne_gTok : gA ≠ gTok := fun h => gTok_ne_gA h.symm

/-! ## Bits of the encoded values -/

theorem enc_int_pos {z : ℤ} (hz : 0 ≤ z) :
    (Val.int z).enc = Glyph.pos :: (Computability.encodeNat z.natAbs).map Glyph.bit ++ [Glyph.iend] := by
  rw [enc_int]
  simp [not_lt.mpr hz]

theorem enc_int_neg {z : ℤ} (hz : z < 0) :
    (Val.int z).enc = Glyph.neg :: (Computability.encodeNat z.natAbs).map Glyph.bit ++ [Glyph.iend] := by
  rw [enc_int]; simp [hz]

theorem encodeNat_map_bit_length (n : ℕ) : ((Computability.encodeNat n).map Glyph.bit).length = n.size := by
  rw [List.length_map, encodeNat_length]

/-- `ofBits` of the least-significant-first bit list of `n` is `n`. -/
theorem ofBits_bits_eq (n : ℕ) : ofBits n.bits = n := ofBits_bits n

/-- The bit list of `n` is canonical. -/
theorem isBits_bits_eq (n : ℕ) : IsBits n.bits := isBits_bits n

/-- Canonical least-significant-first bit list of `2^k`: `k` zeros then a one. -/
theorem bits_two_pow (k : ℕ) : (2 ^ k).bits = List.replicate k false ++ [true] := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
    rw [h, Nat.bit0_bits _ (pow_ne_zero k (by norm_num)), ih]
    simp [List.replicate_succ]

theorem size_two_pow (k : ℕ) : (2 ^ k).size = k + 1 := Nat.size_pow

/-- For nonnegative integers the absolute value is the `toNat`. -/
theorem natAbs_of_nonneg' {z : ℤ} (hz : 0 ≤ z) : z.natAbs = z.toNat := by
  have h : z = ((z.toNat : ℕ) : ℤ) := (Int.toNat_of_nonneg hz).symm
  conv_lhs => rw [h]
  exact Int.natAbs_natCast _

theorem isz_nonneg (z : ℤ) : 2 ≤ isz z := by rw [isz_eq]; omega

/-- `Nat.clog 2 n` is the bit-size of `n - 1` (and `0` at `n = 0`). -/
theorem clog_two_eq_size_sub_one {n : ℕ} (hn : 1 ≤ n) : Nat.clog 2 n = (n - 1).size := by
  have key : ∀ k : ℕ, (n - 1).size ≤ k ↔ Nat.clog 2 n ≤ k := by
    intro k
    rw [Nat.size_le, Nat.clog_le_iff_le_pow (by norm_num)]
    have h2 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    omega
  exact le_antisymm ((key _).mp le_rfl) ((key _).mpr le_rfl)

/-- Integer form of the previous lemma, for `a ≥ 1`. -/
theorem clog_two_int {a : ℤ} (ha : 1 ≤ a) :
    (Nat.clog 2 a.toNat : ℤ) = ((a - 1).natAbs.size : ℤ) := by
  have ha0 : (0 : ℤ) ≤ a := by omega
  have h1 : 1 ≤ a.toNat := by
    have hcast : (a.toNat : ℤ) = a := Int.toNat_of_nonneg ha0
    omega
  have h2 : (a - 1).natAbs = a.toNat - 1 := by
    have hcast : a = (a.toNat : ℤ) := (Int.toNat_of_nonneg ha0).symm
    rw [hcast]
    exact Int.natAbs_natCast_sub_natCast_of_ge h1
  rw [clog_two_eq_size_sub_one h1, h2]

end Size
end Work.IntLib
