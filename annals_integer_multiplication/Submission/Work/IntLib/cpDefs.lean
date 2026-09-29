import Mathlib
import Submission.Work.IntLib.chunkDefs
import Submission.Work.IntLib.UR.Defs

/-!
# IntLib: definitions for `unaryCopyV2`

`Work.IntLib.unaryCopyV2` copies the unary counter `Unary m Ca` from stack `a` to stack `b`
(whose tail is `gEnd :: Cb`), restoring stack `a` and every other stack, in time `O(m+1)`.

The program (parameterised by a scratch stack `c` distinct from `a` and `b`, and using the
loop register `rD` of `Work.IntLib.UR`):

1. push a `gEnd` marker on the scratch stack `c` (so that `c` becomes the counter `Unary 0 (X c)`);
2. `cpLoop a b c`: while the head of `a` is a token, pop it off `a` and push it on **both** `c`
   and `b`; this empties `a` (down to its own `gEnd`) and turns `c` into `Unary m (X c)` while
   turning `b` into `Unary m Cb`;
3. `urPhase1Loop c a` moves the `m` tokens of `c` back onto `a` (which is `Unary 0 Ca`, so it
   becomes `Unary m Ca`), leaving `c = Unary 0 (X c)`; a final `pop` removes the marker.

`cpBody`/`cpLoop` are the only new program pieces; the second phase reuses `UR.urPhase1Loop`.
-/

set_option autoImplicit false

namespace Work.IntLib

open HvdH

/-- Body of the copy loop: pop one token from `a`, push it on `c` and on `b`, then peek the new
head of `a` into the loop register `rD`. -/
def cpBody (a b c : Stk) : Cmd :=
  .seq (.pop a UR.rD) (.seq (.push c UR.rD) (.seq (.push b UR.rD) (.peek a UR.rD)))

/-- The copy loop: while `reg rD = gTok`, run `cpBody`. -/
def cpLoop (a b c : Stk) : Cmd := .loop UR.rD gTok (cpBody a b c)

/-- The whole `unaryCopyV2` program. -/
def cpProg (a b c : Stk) : Cmd :=
  .seq (.set UR.rD gEnd)
    (.seq (.push c UR.rD)
      (.seq (.peek a UR.rD)
        (.seq (cpLoop a b c)
          (.seq (.peek c UR.rD)
            (.seq (UR.urPhase1Loop c a) (.pop c UR.rD))))))

end Work.IntLib
