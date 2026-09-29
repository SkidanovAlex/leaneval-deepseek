import Mathlib

namespace Work.Kernel

/-- `Computability.encodePosNum` is `Nat.bits` of the underlying natural number. -/
theorem encodeNatBits_encodePosNum (p : PosNum) :
    Computability.encodePosNum p = (p : ℕ).bits := by
  induction p with
  | one => simp [Computability.encodePosNum, Nat.one_bits]
  | bit0 q ih =>
      rw [Computability.encodePosNum, ih, PosNum.cast_bit0,
        show ((q : ℕ) + (q : ℕ)) = 2 * (q : ℕ) by ring,
        Nat.bit0_bits _ (Nat.ne_of_gt (PosNum.cast_pos q))]
  | bit1 q ih =>
      rw [Computability.encodePosNum, ih, PosNum.cast_bit1,
        show ((q : ℕ) + (q : ℕ) + 1) = 2 * (q : ℕ) + 1 by ring, Nat.bit1_bits]

/-- `Computability.encodeNum` is `Nat.bits` of the underlying natural number. -/
theorem encodeNatBits_encodeNum (m : Num) :
    Computability.encodeNum m = (m : ℕ).bits := by
  induction m with
  | zero => simp [Computability.encodeNum, Nat.zero_bits]
  | pos p => simpa [Computability.encodeNum] using encodeNatBits_encodePosNum p

/-- `Computability.encodeNat` is `Nat.bits`. -/
theorem encodeNatBits_eq_bits : Computability.encodeNat = Nat.bits := by
  funext n
  show Computability.encodeNum (↑n : Num) = n.bits
  rw [encodeNatBits_encodeNum]
  exact congrArg Nat.bits (Num.to_of_nat n)

/-- `import Mathlib` only (this must stay a *Kernel-level* module: do not import anything under `Submission/Work/IntLib` or `Submission/Work/Main`, the dependency order is Kernel ← IntLib/Main).  `Computability.encodeNat : ℕ → List Bool` is Mathlib's binary encoding (`encodeNum` of the coercion `ℕ → Num`): `encodePosNum one = [true]`, `encodePosNum (bit0 p) = false :: encodePosNum p`, `encodePosNum (bit1 p) = true :: encodePosNum p`, `encodeNum zero = []`.  `Nat.bits` is `Nat.binaryRec [] (fun b _ ih => b :: ih)`.  Prove they agree.  Helpers in this file must be named with the prefix `encodeNatBits_`.  (Useful Mathlib facts: `PosNum.cast_pos`, `PosNum.cast_bit0`, `PosNum.cast_bit1`, `Num.to_of_nat`, `Nat.one_bits`, `Nat.bit0_bits`, `Nat.bit1_bits`, `Nat.zero_bits`.) -/
theorem encodeNatBits (n : ℕ) : Computability.encodeNat n = n.bits := by
  rw [encodeNatBits_eq_bits]

end Work.Kernel
