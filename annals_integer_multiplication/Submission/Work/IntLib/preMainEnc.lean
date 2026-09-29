import Mathlib
import Submission.Work.IntLib.chunkProg
import Submission.Work.IntLib.drainCost

/-!
# Encoding facts for the `chunk` pre-phase

Small rewrite lemmas about `Val.enc (.int (n : ℤ))` used by the pre-phase proof
(`Submission/Work/IntLib/preMainPhaseV2.lean`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.IntLib

open HvdH

/-- The encoding of a natural number cast to `ℤ`. -/
theorem enc_natCast (n : ℕ) :
    Val.enc (.int (n : ℤ)) = Glyph.pos :: (n.bits.map Glyph.bit ++ [Glyph.iend]) := by
  rw [enc_int, encodeNat_eq_bits, Int.natAbs_natCast,
    if_neg (not_lt.mpr (Int.natCast_nonneg n))]

/-- The reverse of that encoding, in the shape produced by a `Shift.drain`. -/
theorem enc_natCast_reverse (n : ℕ) :
    (Val.enc (.int (n : ℤ))).reverse =
      Glyph.iend :: (n.bits.reverse.map Glyph.bit ++ [Glyph.pos]) := by
  simp [enc_natCast]

/-- Its length. -/
theorem enc_natCast_length (n : ℕ) : (Val.enc (.int (n : ℤ))).length = n.size + 2 := by
  rw [vsz_int, isz_eq, Int.natAbs_natCast]

theorem isz_natCast (n : ℕ) : isz (n : ℤ) = n.size + 2 := by
  rw [isz_eq, Int.natAbs_natCast]

/-- No `Val` encoding contains a frame marker. -/
theorem noMark_enc_natCast (n : ℕ) : Shift.NoMark (Val.enc (.int (n : ℤ))) :=
  noMark_enc_int _

end Work.IntLib
