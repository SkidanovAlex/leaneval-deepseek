import Mathlib
import Submission.Work.Kernel.Raw
import Submission.Work.Layout.Move

/-!
# Kernel: the `roll` program family

`HvdH.KernelLib.roll`: move the `k`-th value of the value stack (0 = top) to the top.

The program is built from the *marker movers* of the Layout area (`Work.Layout.mvVal_ev_full`) and
one loop-free block:

* `roll_mvSeq a b c d m` runs `Work.Layout.mvVal a b c d` `m` times, i.e. it moves the top `m`
  values of stack `a` onto stack `b` — each one in normal order, so the block is *reversed* — at
  cost `O(Σ vsz)` (`Submission/Work/Kernel/rollMvSeqEv.lean`), restoring the scratch stacks `c`,`d`;
* `roll_prog k` = save the top `k` values on `roll_stkA`, move the now exposed `k`-th value to
  `roll_stkB`, move the `k` saved values back, and finally put the saved value back on top.

Every value is moved at most twice, so the cost is `O((k+1) * (Σ_{i≤k} vsz + 1))`.
-/

set_option autoImplicit false

namespace Work.Kernel

open HvdH

/-- Run `Work.Layout.mvVal a b c d` `m` times: move the top `m` values of stack `a` to stack `b`
(the block comes out reversed), touching only `a`, `b`, `c`, `d`. -/
def roll_mvSeq (a b c d : Stk) : ℕ → Cmd
  | 0 => .skip
  | (m + 1) => .seq (Work.Layout.mvVal a b c d) (roll_mvSeq a b c d m)

@[simp] theorem roll_mvSeq_zero (a b c d : Stk) : roll_mvSeq a b c d 0 = Cmd.skip := rfl

@[simp] theorem roll_mvSeq_succ (a b c d : Stk) (m : ℕ) :
    roll_mvSeq a b c d (m + 1) = .seq (Work.Layout.mvVal a b c d) (roll_mvSeq a b c d m) := rfl

/-- Scratch stack receiving the `k` values saved above the `k`-th one. -/
def roll_stkA : Stk := 1

/-- Scratch stack receiving the `k`-th value. -/
def roll_stkB : Stk := 2

/-- First `mvVal` scratch stack (pending-subtree counter). -/
def roll_stkC : Stk := 4

/-- Second `mvVal` scratch stack (reversal buffer). -/
def roll_stkD : Stk := 5

/-- The `roll` program: save the top `k` values on `roll_stkA`, move the exposed `k`-th value to
`roll_stkB`, restore the `k` saved values, and put the saved `k`-th value back on top. -/
def roll_prog (k : ℕ) : Cmd :=
  .seq (roll_mvSeq 0 roll_stkA roll_stkC roll_stkD k)
    (.seq (Work.Layout.mvVal 0 roll_stkB roll_stkC roll_stkD)
      (.seq (roll_mvSeq roll_stkA 0 roll_stkC roll_stkD k)
        (Work.Layout.mvVal roll_stkB 0 roll_stkC roll_stkD)))

end Work.Kernel
