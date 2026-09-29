import Mathlib
import Submission.Work.IntLib.divRaw

/-!
# Evaluation of one ripple-subtraction step (`subBitProg`)

`subBitProg rr rb rc rs` is the 8-case decision tree of a single ripple-subtraction step:
registers `rr`, `rb` hold the operand bits, `rc` the incoming borrow.  The tree overwrites
`rs` with the result bit and `rc` with the outgoing borrow; every path is three `ite` tests
plus two `set`s, hence cost 5.

The arithmetic content is that the two `Bool` functions `subBitVal`/`subBorrow` agree with the
branch that the tree selects for each of the 8 combinations of `(x, y, c)`.  After the case
split the remaining proof is uniform: at each of the three levels `ite` chooses its branch
according to the corresponding hypothesis (`s.reg r = bit b` either matches `bit true`, giving
`Eval.iteT`, or contradicts it, giving `Eval.iteF`), and the innermost two `set`s are chained
with `Eval.seq`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.IntLib

open HvdH

theorem eval_subBitProg (main : HvdH.Cmd) (rr rb rc rs : HvdH.Reg) (s : HvdH.State)
    (x y c : Bool) (hrr : s.reg rr = HvdH.Glyph.bit x) (hrb : s.reg rb = HvdH.Glyph.bit y)
    (hrc : s.reg rc = HvdH.Glyph.bit c) :
    HvdH.Eval main (Work.IntLib.subBitProg rr rb rc rs) s
      ((s.updReg rs (HvdH.Glyph.bit (Work.IntLib.subBitVal x y c))).updReg rc
        (HvdH.Glyph.bit (Work.IntLib.subBorrow x y c))) 5 := by
  -- 8 cases; in each the `Bool` expressions `subBitVal`/`subBorrow` reduce to literals and the
  -- three `ite` levels pick their branch, so one tactic block closes every case.
  rcases x <;> rcases y <;> rcases c <;>
  simp only [Work.IntLib.subBitProg, Work.IntLib.subBitVal, Work.IntLib.subBorrow,
    Bool.toNat_true, Bool.toNat_false, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod,
    Nat.reduceBEq, Nat.reduceGT, decide_true, decide_false] <;>
  (first | refine HvdH.Eval.iteT hrr ?_ | refine HvdH.Eval.iteF (by rw [hrr]; decide) ?_) <;>
  (first | refine HvdH.Eval.iteT hrb ?_ | refine HvdH.Eval.iteF (by rw [hrb]; decide) ?_) <;>
  (first | refine HvdH.Eval.iteT hrc ?_ | refine HvdH.Eval.iteF (by rw [hrc]; decide) ?_) <;>
  exact HvdH.Eval.seq (HvdH.Eval.set rs _ s) (HvdH.Eval.set rc _ _)

end Work.IntLib
