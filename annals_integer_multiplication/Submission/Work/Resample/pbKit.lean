import Mathlib
import Submission.Work.Layout.Base
import Submission.Work.Layout.Move
import Submission.Work.Layout.mvVal_ev_full
import Submission.Work.Layout.ReplicateDefs
import Submission.Work.Resample.pbDefs

/-!
# Stack words for `Work.Resample.pbWords`: shared definitions

The six conjuncts of `Work.Resample.pbWords` are value-stack words moving single values between
stack 0 and another stack, duplicating the top of stack 0, and multiplying the elements of a list
of naturals held on stack 2.  Everything is built from the marker-based movers of the Layout area
(`Work.Layout.mvA`, `mvB`, `mvVal`, `drain2`), whose `Ev`-level specs (`mvA_ev`, `mvB_ev`,
`mvVal_ev`, `mvVal_ev_full`) are already proved there.

This file only fixes the programs; the `Ev`/`WordM` proofs live elsewhere.

* `pbCopy` — the copy word `seqs [mvA a c d, drain2 c b a]`: it writes the top value of stack `a`
  on stack `b`, restoring `a` (the `drain2` loop pushes every glyph it moves back on **both**
  `b` and `a`, which is what makes it a duplication rather than a move).
* `pbFoldLoop mulP` — the loop that walks a `cons`-chain list of naturals sitting on stack 7,
  takes its elements off one by one and multiplies them into the accumulator on top of stack 0
  with the multiplier word `mulP`.  The list is *copied* onto stack 7 beforehand, so stack 2
  keeps its original content.
* `pbProdProg mulP` — copy the list value from stack 2 to stack 7, then fold.
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH
open Work.Layout

/-! ## Stacks and registers -/

/-- the pile holding the copy of the list while it is folded -/
def pbElt : Stk := 7
/-- scratch stacks for the `mvVal` moves inside the fold loop -/
def pbV1 : Stk := 3
def pbV2 : Stk := 4
/-- scratch stacks of the list copy -/
def pbC1 : Stk := 5
def pbC2 : Stk := 6
/-- the loop-test register of the fold loop (mvVal uses registers 0–4) -/
def pbR : Reg := 9

/-! ## The copy word -/

/-- Copy the top value of stack `a` onto stack `b`, restoring `a`. -/
def pbCopy (a b c d : Stk) : Cmd := seqs [mvA a c d, drain2 c b a]

/-! ## The fold loop -/

/-- One iteration of the fold: look at the head glyph of the counter pile `pbElt`; at `nil`
consume it and stop, at `cons` consume it, move the exposed factor onto the value stack, multiply
it into the accumulator and continue. -/
def pbFoldBody (mulP : Cmd) : Cmd :=
  seqs [Cmd.peek pbElt pbR,
        Cmd.ite pbR Glyph.cons
          (seqs [Cmd.pop pbElt pbR, mvVal pbElt 0 pbV1 pbV2, mulP, Cmd.set pbR Glyph.cons])
          (seqs [Cmd.pop pbElt pbR, Cmd.set pbR Glyph.nil])]

/-- The fold loop: its body runs while the head glyph of `pbElt` is `cons`. -/
def pbFoldLoop (mulP : Cmd) : Cmd := Cmd.loop pbR Glyph.cons (pbFoldBody mulP)

/-- The fold loop with the loop register initialised. -/
def pbFoldProg (mulP : Cmd) : Cmd := Cmd.seq (Cmd.set pbR Glyph.cons) (pbFoldLoop mulP)

/-- Make a copy of the list value on stack 2 and fold its elements into the accumulator on stack 0
with the multiplier `mulP`. -/
def pbProdProg (mulP : Cmd) : Cmd := seqs [pbCopy 2 pbElt pbC1 pbC2, pbFoldProg mulP]

end Work.Resample
