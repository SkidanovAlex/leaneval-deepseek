import Mathlib
import Submission.Work.PTCert.EntryDefs

open Submission.PTCert Submission.PTCert.G Submission.PTCert.D

namespace Work.PTCert

/-- The Klein group `(ℤ/2)^2` is indexed by `a < 4` through `bval` (`bval b = (b 0).val + 2*(b 1).val`)
and by the bits of `a` through `zOfSc` (`zOfSc sc i = sbit sc i.val`); on the four vectors the two
readings agree.  (`sbit a 0 = a % 2`, `sbit a 1 = (a / 2) % 2 = a / 2` for `a < 4`.) -/
theorem bval_zOfSc (a : ℕ) (ha : a < 4) : bval (zOfSc (m := 2) a) = a := by
  have h0 : (zOfSc (m := 2) a 0).val = a % 2 := by
    show ((sbit a (0 : Fin 2).val : ℕ) : ZMod 2).val = a % 2
    rw [ZMod.val_natCast]
    simp [sbit]
  have h1 : (zOfSc (m := 2) a 1).val = (a / 2) % 2 := by
    show ((sbit a (1 : Fin 2).val : ℕ) : ZMod 2).val = (a / 2) % 2
    rw [ZMod.val_natCast]
    simp [sbit, Nat.shiftRight_eq_div_pow]
  unfold bval
  rw [h0, h1]
  omega

end Work.PTCert
