import Mathlib
import Submission.Work.IntLib.AddSub.Defs
import Submission.Work.IntLib.AddSub.Basic
import Submission.Work.IntLib.AddSub.EvKit

/-!
# `IntLib` / add–sub: the chunks of `asw_setup`

`asw_setup fp` is a straight line program of 25 commands.  We split it into five chunks:

* `Lmark`   — push the frame marker `gmk k` on each of the seven scratch stacks;
* `LsignA`  — pop the sign of `a` (top of stack 0) onto `sSgA`;
* `Lparse k`— move one encoded value off stack 0: drain up to its `iend` through `sBuf`,
              drop the `iend`, then drain `sBuf` onto the magnitude stack `k`;
* `Lfp fp`  — pop the sign of `b`, run `fp` (which flips it), push it onto `sSgB`;
* `Lparse sB` — as above for the second value.

`asw_setup_eq` records that these five chunks, in this order, are exactly `asw_setup fp`.
-/

set_option autoImplicit false

namespace Work.IntLib.AddSub

open HvdH

/-- The 14 marker-pushing commands at the head of `asw_setup`: for each scratch stack `k`,
`set rA (gmk k); push k rA`. -/
abbrev Lmark : List Cmd :=
  [.set rA (gmk sBuf), .push sBuf rA,
   .set rA (gmk sA), .push sA rA,
   .set rA (gmk sB), .push sB rA,
   .set rA (gmk sO1), .push sO1 rA,
   .set rA (gmk sO2), .push sO2 rA,
   .set rA (gmk sSgA), .push sSgA rA,
   .set rA (gmk sSgB), .push sSgB rA]

/-- Pop the sign glyph of the first operand (top of stack 0) and push it onto `sSgA`. -/
abbrev LsignA : List Cmd := [.pop 0 rB, .push sSgA rB]

/-- Move one encoded magnitude off stack 0 onto the scratch stack `k`: drain stack 0 up to
its `iend` through `sBuf` (reversing), drop the `iend`, then drain `sBuf` (which reverses
again) onto `k`.  The marker `gmk sBuf` of `sBuf` stays in place. -/
abbrev Lparse (k : Stk) : List Cmd :=
  [asw_drain 0 sBuf Glyph.iend rT rF, .pop 0 rT, asw_drain sBuf k (gmk sBuf) rT rF]

/-- Pop the sign glyph of the second operand, apply `fp` to it (flipping it), push the
result onto `sSgB`. -/
abbrev Lfp (fp : Cmd) : List Cmd := [.pop 0 rB, fp, .push sSgB rB]

/-- `asw_setup` is the concatenation of the five chunks. -/
theorem asw_setup_eq (fp : Cmd) :
    asw_setup fp = seqs (Lmark ++ (LsignA ++ (Lparse sA ++ (Lfp fp ++ Lparse sB)))) := rfl

end Work.IntLib.AddSub
