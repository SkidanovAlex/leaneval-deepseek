import Submission.Work.IntLib.SqrtGcd.Basic
import Submission.Work.IntLib.SqrtGcd.SubProg
import Submission.Work.IntLib.SqrtGcd.SqrtProg
import Submission.Work.IntLib.SqrtGcd.GcdDefs
import Submission.Work.IntLib.SqrtGcd.Dup

/-!
# The binary gcd (program layer)

Stack layout:

| stack | content |
|-------|---------|
| 0     | the value stack |
| `sU` = 1 | `u`, least significant first (canonical) |
| `sV` = 2 | `v`, least significant first (canonical) |
| `sG` = 3 | a unary counter: `g` copies of `gTick` |
| `sP` = 4, `sQ` = 5 | scratch bit regions |
| `sR` = 6 | the temporary of the copy operations |
| `sS` = 7 | the output of the ripple subtracter |

Registers: `rgT`=0, `rgX`=1, `rgY`=2, `rgZ`=3, `rgC`=4 (borrow), `rgF`=5 (loop flag),
`rgU`=6, `rgW`=7 (inner loop flag), `rgS1`=8 (saved borrow).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.IntLib
namespace SG

open HvdH Work.Layout

def sU : Stk := 1
def sV : Stk := 2
def sG : Stk := 3

def rgS1 : Reg := 8

/-- Strip the leading `false` bits of `sS`, stop if it then holds `0`, otherwise replace the region
of `dst` by `oddPart` of its value. -/
def gcdTake (dst : Stk) : Cmd :=
  seqs [ stripZeros sS rgT,
         .peek sS rgT,
         .ite rgT (.mk sS) (.set rgF gStop)
           (seqs [ rLoop sS (.mk sS) (some sP) rgT, stripZeros sP rgT,
                   rLoop dst (.mk dst) none rgT, moveSame sP dst sQ rgT,
                   .set rgF gGo ]) ]

/-- One binary-gcd iteration. -/
def gcdBody : Cmd :=
  seqs [
    .set rgF gGo,
    dup2 sU sP sR sS rgT,
    dup2 sV sQ sR sS rgT,
    subLoop sP sQ (.mk sP) (.mk sQ) sS rgX rgY rgC rgZ rgT rgU rgW,
    .mov rgS1 rgC,
    .ite rgS1 (.bit true)
      (seqs [ rLoop sS (.mk sS) none rgT,
              dup2 sV sP sR sS rgT, dup2 sU sQ sR sS rgT,
              subLoop sP sQ (.mk sP) (.mk sQ) sS rgX rgY rgC rgZ rgT rgU rgW,
              gcdTake sV ])
      (gcdTake sU) ]

def gcdMain : Cmd := .seq (.set rgF gGo) (.loop rgF gGo gcdBody)

/-- Strip the leading `false` bits of both regions (`u` and `v` become odd). -/
def gcdOdd : Cmd := seqs [ stripZeros sU rgT, stripZeros sV rgT ]

/-- Strip the factors of `2` common to `u` and `v`, counting them in `sG`. -/
def gcdPhaseA : Cmd :=
  .seq (.set rgF gGo)
    (.loop rgF gGo
      (.seq (.peek sU rgT) (.seq (.peek sV rgU)
        (.ite rgT (.bit false)
          (.ite rgU (.bit false)
            (seqs [ .pop sU rgT, .pop sV rgU, .set rgW gTick, .push sG rgW,
                    .set rgF gGo ])
            (.set rgF gStop))
          (.set rgF gStop)))))

/-- Multiply `u` by `2 ^ g` (the counter `sG`), by pushing a `false` bit per tick. -/
def gcdScale : Cmd :=
  .seq (.set rgF gGo)
    (.loop rgF gGo
      (.seq (.peek sG rgT)
        (.ite rgT gTick
          (seqs [ .pop sG rgT, .set rgU (.bit false), .push sU rgU, .set rgF gGo ])
          (.set rgF gStop))))

/-- Set up the scratch stacks and parse the two values (their magnitudes) into `sU`, `sV`. -/
def gcdSetup : Cmd :=
  seqs [ mkPush sU rgT, mkPush sV rgT, mkPush sG rgT, mkPush sP rgT, mkPush sQ rgT,
         mkPush sR rgT, mkPush sS rgT,
         .pop 0 rgU, parseTo sP rgU rgZ rgF, .pop 0 rgU, rLoop sP (.mk sP) (some sU) rgT,
         .pop 0 rgU, parseTo sP rgU rgZ rgF, .pop 0 rgU, rLoop sP (.mk sP) (some sV) rgT ]

/-- The whole computation after the setup. -/
def gcdRun : Cmd :=
  seqs [ gcdPhaseA,
         .peek sU rgT,
         .ite rgT (.mk sU)
           (seqs [ moveSame sV sU sR rgT, gcdScale ])
           (seqs [ .peek sV rgU,
                   .ite rgU (.mk sV) gcdScale
                     (seqs [ gcdOdd, gcdMain, gcdScale ]) ]) ]

/-- Emit the value of `sU` (a bit region of any value) on top of stack 0, canonically (leading
zero bits are dropped). -/
def gcdFinish : Cmd :=
  seqs [ rLoop sU (.mk sU) (some sP) rgT,
         stripZeros sP rgT,
         .set rgU .iend, .push 0 rgU,
         rLoop sP (.mk sP) (some 0) rgT,
         .set rgU .pos, .push 0 rgU ]

/-- Restore the scratch stacks. -/
def gcdClean : Cmd :=
  seqs [ rLoop sU (.mk sU) none rgT, rLoop sV (.mk sV) none rgT, rLoop sG (.mk sG) none rgT,
         rLoop sP (.mk sP) none rgT, rLoop sQ (.mk sQ) none rgT, rLoop sR (.mk sR) none rgT,
         rLoop sS (.mk sS) none rgT,
         .pop sU rgT, .pop sV rgT, .pop sG rgT, .pop sP rgT, .pop sQ rgT, .pop sR rgT,
         .pop sS rgT ]

def gcdProg : Cmd := seqs [ gcdSetup, gcdRun, gcdFinish, gcdClean ]

end SG
end Work.IntLib
