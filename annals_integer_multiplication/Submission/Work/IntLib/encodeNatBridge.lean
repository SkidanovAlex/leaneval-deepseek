import Mathlib
import Submission.Work.IntLib.Defs

/-!
# The `Computability.encodeNat` / `Nat.bits` bridge, and the size of integer values

`Computability.encodeNat` (Mathlib's binary encoding of `ℕ` into `List Bool`, least significant
bit first, no leading zeros) agrees with `Nat.bits`, and therefore inherits all of its structural
properties: length `= n.size`, empty iff `n = 0`, last bit `true` for `n ≠ 0`.

Consequently the encoding of an integer value `Val.int z` has length exactly `isz z`, which is the
size bookkeeping used throughout the IntLib cost analysis.
-/

set_option autoImplicit false

namespace Work.IntLib

open HvdH

/-- `encodePosNum` is `Nat.bits` of the underlying natural number. -/
theorem encodePosNum_eq_bits (p : PosNum) : Computability.encodePosNum p = (p : ℕ).bits := by
  induction p with
  | one => simp [Computability.encodePosNum, Nat.one_bits]
  | bit0 q ih =>
      rw [Computability.encodePosNum, ih, PosNum.cast_bit0,
        show ((q : ℕ) + (q : ℕ)) = 2 * (q : ℕ) by ring,
        Nat.bit0_bits _ (Nat.ne_of_gt (PosNum.cast_pos q))]
  | bit1 q ih =>
      rw [Computability.encodePosNum, ih, PosNum.cast_bit1,
        show ((q : ℕ) + (q : ℕ) + 1) = 2 * (q : ℕ) + 1 by ring, Nat.bit1_bits]

/-- `encodeNum` is `Nat.bits` of the underlying natural number. -/
theorem encodeNum_eq_bits (m : Num) : Computability.encodeNum m = (m : ℕ).bits := by
  induction m with
  | zero => simp [Computability.encodeNum, Nat.zero_bits]
  | pos p => simpa [Computability.encodeNum] using encodePosNum_eq_bits p

/-- `Computability.encodeNat` is `Nat.bits`. -/
theorem encodeNat_eq_bits : Computability.encodeNat = Nat.bits := by
  funext n
  show Computability.encodeNum (↑n : Num) = n.bits
  rw [encodeNum_eq_bits]
  exact congrArg Nat.bits (Num.to_of_nat n)

theorem encodeNat_length (n : ℕ) : (Computability.encodeNat n).length = n.size := by
  rw [encodeNat_eq_bits]; exact Nat.size_eq_bits_len n

theorem encodeNat_eq_nil_iff (n : ℕ) : Computability.encodeNat n = [] ↔ n = 0 := by
  rw [encodeNat_eq_bits]
  simpa using (bits_ne_nil_iff (n := n)).not

theorem encodeNat_getLast?_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    (Computability.encodeNat n).getLast? = some true := by
  rw [encodeNat_eq_bits]; exact bits_getLast?_of_ne_zero hn

/-- Unfolding of the encoding of an integer value. -/
theorem enc_int (z : ℤ) : (Val.int z).enc =
    (if z < 0 then Glyph.neg else Glyph.pos) ::
      ((Computability.encodeNat z.natAbs).map Glyph.bit ++ [Glyph.iend]) := rfl

theorem isz_eq (z : ℤ) : isz z = z.natAbs.size + 2 := rfl

/-- Size of an integer value is `isz`. -/
theorem vsz_int (z : ℤ) : (Val.int z).enc.length = isz z := by
  simp only [enc_int, isz_eq, List.length_cons, List.length_append, List.length_map,
    List.length_nil, encodeNat_length]

theorem encodeNatBridge : Computability.encodeNat = Nat.bits ∧ (∀ n : ℕ, (Computability.encodeNat n).length = n.size) ∧ (∀ n : ℕ, Computability.encodeNat n = [] ↔ n = 0) ∧ (∀ n : ℕ, n ≠ 0 → (Computability.encodeNat n).getLast? = some true) ∧ (∀ z : ℤ, (HvdH.Val.int z).enc = (if z < 0 then HvdH.Glyph.neg else HvdH.Glyph.pos) :: ((Computability.encodeNat z.natAbs).map HvdH.Glyph.bit ++ [HvdH.Glyph.iend])) ∧ (∀ z : ℤ, HvdH.isz z = z.natAbs.size + 2) ∧ (∀ z : ℤ, (HvdH.Val.int z).enc.length = HvdH.isz z) := by
  exact ⟨encodeNat_eq_bits, encodeNat_length, encodeNat_eq_nil_iff,
    fun n hn => encodeNat_getLast?_of_ne_zero hn, enc_int, isz_eq, vsz_int⟩

end Work.IntLib
