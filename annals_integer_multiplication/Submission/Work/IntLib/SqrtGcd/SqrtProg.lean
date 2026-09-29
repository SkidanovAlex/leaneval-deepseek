import Submission.Work.IntLib.SqrtGcd.Basic
import Submission.Work.IntLib.SqrtGcd.SubProg
import Submission.Work.IntLib.SqrtGcd.SqrtDefs
import Submission.Work.IntLib.SqrtGcd.Dup

/-!
# The integer square root (program layer)

Stack layout (marker `mk k` at the bottom of every region):

| stack | content |
|-------|---------|
| 0     | the value stack |
| `sA` = 1 | the radicand bits, **most significant first** (padded to even length) |
| `sB` = 2 | the current remainder `rem = s - r^2`, least significant first |
| `sC` = 3 | the current root `r`, least significant first |
| `sP` = 4, `sQ` = 5, `sR` = 6, `sS` = 7 | scratch |

Registers: `rgT` = 0 (glyph moves), `rgX` = 1, `rgY` = 2 (the bit pair), `rgZ` = 3 (parity /
digit scratch), `rgC` = 4 (borrow), `rgF` = 5 (outer loop flag), `rgU` = 6 (scratch), `rgW` = 7
(inner loop flag).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.IntLib
namespace SG

open HvdH Work.Layout

def rgU : Reg := 6
def rgW : Reg := 7

/-- Push the marker of stack `k`. -/
def mkPush (k : Stk) (r : Reg) : Cmd := .seq (.set r (.mk k)) (.push k r)

/-- Flip a register between `bit false` and `bit true`. -/
def toggle (r : Reg) : Cmd := .ite r (.bit true) (.set r (.bit false)) (.set r (.bit true))

/-- One step of the parse loop: pop a glyph of stack 0; at `iend` push it back and stop, otherwise
push it on `dst` and flip the parity register. -/
def parseBody (dst : Stk) (r rP rF : Reg) : Cmd :=
  .seq (.pop 0 r)
    (.ite r .iend (.seq (.push 0 r) (.set rF gStop))
      (.seq (.push dst r) (.seq (toggle rP) (.set rF gGo))))

/-- Parse the magnitude bits of the value on top of stack 0 (least significant first there) onto
`dst` (**most significant first**), counting their parity in `rP`. -/
def parseTo (dst : Stk) (r rP rF : Reg) : Cmd :=
  .seq (.set rP (.bit false)) (.seq (.set rF gGo) (.loop rF gGo (parseBody dst r rP rF)))

/-- Move a region preserving its order, through the (empty) scratch stack `tmp`. -/
def moveSame (src : Stk) (dst : Stk) (tmp : Stk) (r : Reg) : Cmd :=
  seqs [ rLoop src (.mk src) (some tmp) r, rLoop tmp (.mk tmp) (some dst) r ]

/-- Copy the region of `src` to `dst` (through the empty scratch `tmp`), keeping `src`. -/
def copy4 (src : Stk) (dst : Stk) (tmp : Stk) (r : Reg) : Cmd :=
  seqs [ rLoop src (.mk src) (some tmp) r, rLoop tmp (.mk tmp) (some src) r,
         rLoop src (.mk src) (some tmp) r, rLoop tmp (.mk tmp) (some dst) r ]

/-- One iteration of the square-root loop (both bits are known to be present). -/
def sqrtWork : Cmd :=
  seqs [
    -- t = 4*root + 1 on sS (root stays on sC)
    dup2 sC sS sP sQ rgT,
    .set rgU (.bit false), .push sS rgU, .set rgU (.bit true), .push sS rgU,
    -- the next bit pair, most significant bit first
    .pop sA rgX, .pop sA rgY,
    -- rem_new = 4*rem + 2*bhi + blo on sQ
    moveSame sB sQ sP rgT,
    .push sQ rgX, .push sQ rgY,
    -- a duplicate of rem_new on sR
    dup2 sQ sR sP sB rgT,
    -- subtract: sR - sS -> sP, borrow in rgC
    subLoop sR sS (.mk sR) (.mk sS) sP rgX rgY rgC rgZ rgT rgU rgW,
    -- branch on the borrow
    .ite rgC (.bit true)
      (seqs [ rLoop sP (.mk sP) none rgT,
              rLoop sQ (.mk sQ) (some sP) rgT, rLoop sP (.mk sP) (some sB) rgT,
              .set rgU (.bit false), .push sC rgU ])
      (seqs [ rLoop sB (.mk sB) none rgT,
              rLoop sQ (.mk sQ) none rgT,
              rLoop sP (.mk sP) (some sB) rgT,
              .set rgU (.bit true), .push sC rgU ]) ]

/-- One step of the square-root loop: stop when the radicand bits are exhausted. -/
def sqrtBody : Cmd :=
  .seq (.peek sA rgT)
    (.ite rgT (.mk sA) (.set rgF gStop) (.seq (.set rgF gGo) sqrtWork))

def sqrtLoop : Cmd := .seq (.set rgF gGo) (.loop rgF gGo sqrtBody)

/-- Set up the scratch stacks and parse the value (assumed nonnegative) into the radicand region. -/
def sqrtSetup : Cmd :=
  seqs [ mkPush sA rgT, mkPush sB rgT, mkPush sC rgT, mkPush sP rgT, mkPush sQ rgT, mkPush sR rgT,
         mkPush sS rgT,
         .pop 0 rgU,
         parseTo sA rgU rgZ rgF,
         .pop 0 rgU,
         .ite rgZ (.bit true) (.seq (.set rgU (.bit false)) (.push sA rgU)) .skip ]

/-- Emit the root (on `sC`) as the value on top of stack 0. -/
def sqrtFinish : Cmd :=
  seqs [ rLoop sC (.mk sC) (some sP) rgT, stripZeros sP rgT,
         .set rgU .iend, .push 0 rgU,
         rLoop sP (.mk sP) (some 0) rgT,
         .set rgU .pos, .push 0 rgU ]

/-- Restore the scratch stacks. -/
def sqrtClean : Cmd :=
  seqs [ rLoop sA (.mk sA) none rgT, rLoop sB (.mk sB) none rgT, rLoop sC (.mk sC) none rgT,
         rLoop sP (.mk sP) none rgT, rLoop sQ (.mk sQ) none rgT, rLoop sR (.mk sR) none rgT,
         rLoop sS (.mk sS) none rgT,
         .pop sA rgT, .pop sB rgT, .pop sC rgT, .pop sP rgT, .pop sQ rgT, .pop sR rgT,
         .pop sS rgT ]

/-- The whole square-root program. -/
def sqrtProg : Cmd := seqs [ sqrtSetup, sqrtLoop, sqrtFinish, sqrtClean ]

end SG
end Work.IntLib
