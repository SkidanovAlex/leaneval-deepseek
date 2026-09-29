import Mathlib
import Submission.Work.Kernel.dropValueDefs

/-!
# `dropValue_chain` acts on the counter region as `pendStep`

The `dropValue` scan keeps its pending-subtree count as a unary region `dropValue_stk1 p w` on stack 1
(`p` copies of `dropValue_tok` above the marker `dropValue_base`, above `w`).  On the glyph `g` just
read from stack 0 the counter moves `p ↦ pendStep g p`, i.e. it opens `pendStep g 1` new tokens when
read from count `1`.

This file records the purely list-theoretic consequence: prepending the tokens opened by `g` to a
region holding `q` tokens yields the region whose count is `pendStep g (q + 1)` (the `q + 1` because
the token consumed by the loop test has already been popped).
-/

set_option autoImplicit false

namespace Work.Kernel

open HvdH

/-- The counter step of a single glyph commutes with shifting the count: reading `g` from the count
`q + 1` opens exactly `pendStep g 1` tokens on top of the `q` tokens that remain. -/
theorem dropValue_pendStep_one_add (g : Glyph) (q : ℕ) :
    pendStep g 1 + q = pendStep g (q + 1) := by
  cases g <;> simp [pendStep] <;> omega

/-- One step of the scan, in list form: pushing the `pendStep g 1` tokens opened by the glyph `g`
onto the counter region that holds `q` tokens gives the counter region of count `pendStep g (q + 1)`. -/
theorem dropValueStk1PendStep (g : HvdH.Glyph) (q : ℕ) (w : List HvdH.Glyph) :
    List.replicate (HvdH.pendStep g 1) Work.Kernel.dropValue_tok ++
        Work.Kernel.dropValue_stk1 q w =
      Work.Kernel.dropValue_stk1 (HvdH.pendStep g (q + 1)) w := by
  have h : HvdH.pendStep g 1 + q = HvdH.pendStep g (q + 1) := dropValue_pendStep_one_add g q
  simp only [dropValue_stk1]
  rw [← h, List.replicate_add, List.append_assoc]

end Work.Kernel
