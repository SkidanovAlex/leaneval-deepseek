import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Kernel.Raw
import Submission.Work.Kernel.Pend
import Submission.Work.Layout.Move
import Submission.Work.Kernel.dup

/-!
# Kernel: definitions for `pick`

`moveTop j a b` moves the top `j` values of stack `a` to the top of stack `b` (the first moved ends
deepest), one `Work.Layout.mvVal` at a time, using stacks `2` and `3` as the buffer / pending counter
(restored by every `mvVal`).

`pickProg k` implements the `pick` field of `KernelLib`: from `vs` with `k < vs.length` it produces
`vs.getD k .nil :: vs`:

1. `moveTop k 0 1` saves the top `k` values on stack 1, exposing the `k`-th value on stack 0;
2. `dup_prog` duplicates the exposed value;
3. `mvVal 0 4 2 3` moves one copy aside on stack 4;
4. `moveTop k 1 0` restores the `k` saved values;
5. `mvVal 4 0 2 3` puts the copy back on top.
-/

set_option autoImplicit false

namespace Work.Kernel

open HvdH

/-- `moveTop j a b`: move the top `j` values of stack `a` onto stack `b` (first moved = deepest),
buffering on stacks `2` and `3`. -/
def moveTop : ℕ → Stk → Stk → Cmd
  | 0, _, _ => Cmd.skip
  | (j+1), a, b => Cmd.seq (Work.Layout.mvVal a b 2 3) (moveTop j a b)

/-- The `pick k` program. -/
def pickProg (k : ℕ) : Cmd :=
  Work.Layout.seqs [moveTop k 0 1, dup_prog, Work.Layout.mvVal 0 4 2 3, moveTop k 1 0,
    Work.Layout.mvVal 4 0 2 3]

end Work.Kernel
