import Mathlib
import Submission.Work.Layout.Base
import Submission.Work.Layout.Move
import Submission.Work.Layout.mvVal_ev_full

set_option autoImplicit false

/-!
# `sortByKey`: definitions for the bottom-up merge sort

Layout of the program (stack indices):

* `0` : the `WordR` value stack (also the target of the key copies for the comparisons);
* `1` : `X`, `2` : `Y` — the source run stacks;
* `3` : `C`, `4` : `D` — the destination run stacks;
* `5` : `T1`, `6` : `T2` — the merge accumulators paired with `C` resp. `D`;
* `7` : `t`, `8` : `d` — scratch stacks for `mvVal`/`mvA`;
* `9` : `Z` — the assembly buffer.

Each run stack holds a list of runs separated by `gMark`s, and below all runs a boundary marker
`gBnd` which separates the run area from the arbitrary junk that was on the stack initially.

Registers `0`–`4` are used by the value movers (`mvA`/`mvB`/`mvVal`) and `rB = 2` by `pushConst`;
the free registers are `rF`(5), `rH`(6), `rI`(7), `rJ`(8), `rK`(9).
-/

namespace Work.Layout
namespace Sk

open HvdH

/-! ## markers and registers -/

/-- boundary marker separating a stack's run area from the junk below it -/
def gBnd : Glyph := .mk 12

/-- loop flag register -/
def rF : Reg := 5
/-- scratch register -/
def rH : Reg := 6
/-- scratch register -/
def rI : Reg := 7
/-- scratch register -/
def rJ : Reg := 8
/-- scratch register (dup loop) -/
def rK : Reg := 9
/-- scratch register (second flag) -/
def rG : Reg := 10

/-! ## abstract list theory -/

/-- encoding of a stack holding the runs `rs` (each terminated by `gMark`) -/
def runEnc (rs : List (List Val)) : List Glyph := (rs.map fun r => encs r ++ [gMark]).flatten

/-- `runEnc` together with the boundary marker that separates the run area from the junk below -/
def runEncB (rs : List (List Val)) : List Glyph := runEnc rs ++ [gBnd]

/-- merge two runs, taking `q`'s head first iff its key is strictly smaller -/
def merge2 : List Val → List Val → List Val
  | [], q => q
  | p, [] => p
  | p :: ps, q :: qs =>
      if pairKey q < pairKey p then q :: merge2 (p :: ps) qs else p :: merge2 ps (q :: qs)

/-- one merge pass on the abstract run lists (processing order = top of stack first).
`toC` says whether the next output run goes to the first destination; the merge of the `i`-th runs of
the two sources goes to the first destination when `i` is even and to the second when `i` is odd,
and the results are pushed in increasing `i`, so each output list is in reverse index order. -/
def passGo : Bool → List (List Val) → List (List Val) → List (List Val) → List (List Val) →
    List (List Val) × List (List Val)
  | true, p :: ps, q :: qs, ac, ad => passGo false ps qs (merge2 p q :: ac) ad
  | false, p :: ps, q :: qs, ac, ad => passGo true ps qs ac (merge2 p q :: ad)
  | true, p :: ps, [], ac, ad => (p :: ac, ad)
  | false, p :: ps, [], ac, ad => (ac, p :: ad)
  | _, [], _qs, ac, ad => (ac, ad)

/-- one merge pass: sources `(ps,qs)` (in stack order), the two components are the outputs -/
def passR (ps qs : List (List Val)) : List (List Val) × List (List Val) := passGo true ps qs [] []

/-- two merge passes -/
def pass2R (ps qs : List (List Val)) : List (List Val) × List (List Val) :=
  let c := passR ps qs
  passR c.1 c.2

/-- the split produced by `distribute` (elements at even positions to the first component) -/
def altGo : List Val → List (List Val) → List (List Val) → List (List Val) × List (List Val)
  | a :: b :: rest, ax, ay => altGo rest ([a] :: ax) ([b] :: ay)
  | [a], ax, ay => ([a] :: ax, ay)
  | [], ax, ay => (ax, ay)

/-- the split of `xs` into runs of length one, distributed alternately -/
def altSplit (xs : List Val) : List (List Val) × List (List Val) := altGo xs [] []

/-! ## the programs -/

/-- drain the values at the top of `S` onto `T` (stops at a non-`cons` glyph) -/
def drainVals (S T t d : Stk) : Cmd :=
  .seq (.peek S rH) (.loop rH Glyph.cons (.seq (mvVal S T t d) (.peek S rH)))

/-- `T` holds `values ++ [gMark]`; push them as a run onto `D` -/
def outRun (T D t d : Stk) : Cmd :=
  .seq (pushConst D gMark) (.seq (drainVals T D t d) (.pop T rJ))

/-- move the top run of `S` onto `D`, using `T` as accumulator -/
def moveRun (S D T t d : Stk) : Cmd :=
  .seq (pushConst T gMark) (.seq (drainVals S T t d) (.seq (.pop S rJ) (outRun T D t d)))

/-- copy the `int` at the top of `S` onto `B`, leaving `S` intact -/
def dupInt (S B T d : Stk) : Cmd :=
  .seq (mvA S T d)
    (.seq (.set rF Glyph.cons)
      (.loop rF Glyph.cons
        (.seq (.pop T rK)
          (.ite rK gMark (.set rF gMark)
            (.seq (.push S rK) (.seq (.push B rK) (.set rF Glyph.cons)))))))

/-- push the bit size of the key of the record at the top of `S` onto the stack `SA`
(the record itself is left intact) -/
def pushSize (pSize : Cmd) (S SA t d : Stk) : Cmd :=
  .seq (.pop S rI)
    (.seq (dupInt S 0 t d)
      (.seq pSize
        (.seq (mvVal 0 SA t d)
          (pushConst S Glyph.cons))))

/-- refresh the cached size of `S`'s front: if `S` still has a record at the top, push its key size -/
def updSize (pSize : Cmd) (S SA t d : Stk) : Cmd :=
  .seq (.peek S rH) (.ite rH Glyph.cons (pushSize pSize S SA t d) .skip)

/-- read the flag value `int 0`/`int 1` at the top of `f` into register `r`: afterwards
`r = Glyph.bit true` iff the flag was `1`; the flag's glyphs are removed from `f` -/
def readFlag (f : Stk) (r : Reg) : Cmd :=
  .seq (.pop f r)
    (.seq (.peek f r)
      (.ite r (Glyph.bit true)
        (.seq (.pop f rJ) (.pop f rJ))
        (.pop f rJ)))

/-- remove the cached sizes from `SA`, up to and including its boundary marker `gMark` -/
def cleanStack (SA : Stk) : Cmd :=
  .seq (.set rF Glyph.cons)
    (.loop rF Glyph.cons
      (.seq (.peek SA rH)
        (.ite rH gMark
          (.seq (.pop SA rJ) (.set rF gMark))
          (.seq (.pop SA rJ) (.set rF Glyph.cons)))))

/-- The merge step with cached key sizes.  The tops of `SA` and `SB` are the bit sizes of the keys of
the fronts of `SX` and `SY`.  Compare them: if they differ, the key of the record whose key has the
smaller size is smaller; if they are equal, compare the keys themselves.  The record with the smaller
key is moved to `T`, and the cached size of the side it came from is refreshed (so the invariant is
restored). -/
def mergeStep (pLt pSize : Cmd) (SX SY SA SB T f1 f2 t d : Stk) : Cmd :=
  seqs [ .pop SX rI,
         .pop SY rJ,
         dupInt SA 0 t d,
         dupInt SB 0 t d,
         pLt,
         mvVal 0 f1 t d,
         dupInt SB 0 t d,
         dupInt SA 0 t d,
         pLt,
         mvVal 0 f2 t d,
         readFlag f1 rH,
         readFlag f2 rG,
         .ite rH (Glyph.bit true)
           (seqs [pushConst SX Glyph.cons, pushConst SY Glyph.cons,
                  mvVal SY T t d, updSize pSize SY SB t d])
           (.ite rG (Glyph.bit true)
             (seqs [pushConst SX Glyph.cons, pushConst SY Glyph.cons,
                    mvVal SX T t d, updSize pSize SX SA t d])
             (seqs [dupInt SX 0 t d, dupInt SY 0 t d, pLt, mvVal 0 f2 t d, readFlag f2 rG,
                    pushConst SX Glyph.cons, pushConst SY Glyph.cons,
                    .ite rG (Glyph.bit true)
                      (seqs [mvVal SY T t d, updSize pSize SY SB t d])
                      (seqs [mvVal SX T t d, updSize pSize SX SA t d])])) ]

/-- body of the merge loop of `mergePair` -/
def mBody (pLt pSize : Cmd) (SX SY SA SB T f1 f2 t d : Stk) : Cmd :=
  .seq
    (.seq (.peek SX rH)
      (.ite rH Glyph.cons
        (.seq (.peek SY rI)
          (.ite rI Glyph.cons (mergeStep pLt pSize SX SY SA SB T f1 f2 t d) (mvVal SX T t d)))
        (.seq (.peek SY rI)
          (.ite rI Glyph.cons (mvVal SY T t d) .skip))))
    (.seq (.peek SX rF) (.ite rF Glyph.cons .skip (.peek SY rF)))

/-- merge the two top runs of `SX`,`SY` onto `D` (via the accumulator `T`); the key sizes of the two
fronts are cached on `SA` and `SB` above a boundary marker -/
def mergePair (pLt pSize : Cmd) (SX SY T D SA SB f1 f2 t d : Stk) : Cmd :=
  seqs [ pushConst T gMark,
         pushConst SA gMark,
         pushConst SB gMark,
         pushSize pSize SX SA t d,
         pushSize pSize SY SB t d,
         .set rF Glyph.cons,
         .loop rF Glyph.cons (mBody pLt pSize SX SY SA SB T f1 f2 t d),
         .pop SX rJ,
         .pop SY rJ,
         outRun T D t d,
         cleanStack SA,
         cleanStack SB ]

/-- body of the merge loop of `pass` -/
def passBody (pLt pSize : Cmd) (X Y C D T1 T2 SA SB f1 f2 t d : Stk) : Cmd :=
  .seq (mergePair pLt pSize X Y T1 C SA SB f1 f2 t d)
    (.seq (.peek Y rH)
      (.ite rH Glyph.cons
        (.seq (mergePair pLt pSize X Y T2 D SA SB f1 f2 t d) (.peek Y rF))
        (.seq (.peek X rH)
          (.seq (.ite rH Glyph.cons (moveRun X D T2 t d) .skip) (.set rF gMark)))))

/-- one merge pass: pair up the runs of `X` and `Y`, writing alternately to `C` and `D` -/
def pass (pLt pSize : Cmd) (X Y C D T1 T2 SA SB f1 f2 t d : Stk) : Cmd :=
  .seq (.peek Y rF)
    (.seq (.loop rF Glyph.cons (passBody pLt pSize X Y C D T1 T2 SA SB f1 f2 t d))
      (.seq (.peek X rH)
        (.ite rH Glyph.cons (moveRun X C T1 t d) .skip)))

/-- two merge passes (returns to the original pair of run stacks) -/
def pass2 (pLt pSize : Cmd) (X Y C D T1 T2 SA SB f1 f2 t d : Stk) : Cmd :=
  .seq (pass pLt pSize X Y C D T1 T2 SA SB f1 f2 t d)
       (pass pLt pSize C D X Y T1 T2 SA SB f1 f2 t d)

/-- body of the distribution loop: one element to `X`, then one to `Y` (if present).
The run terminator `gMark` is pushed *before* the element, so that it ends up below it (a run is
`encs r ++ [gMark]`). -/
def distBody (X Y t d : Stk) : Cmd :=
  .seq (.pop 0 rI)
    (.seq (pushConst X gMark)
      (.seq (mvVal 0 X t d)
        (.seq (.peek 0 rH)
          (.ite rH Glyph.cons
            (.seq (.pop 0 rI)
              (.seq (pushConst Y gMark)
                (.seq (mvVal 0 Y t d) (.peek 0 rH))))
            (.set rH Glyph.nil)))))

/-- split the `cons`-chain on stack 0 into runs of length one on `X` and `Y` -/
def distribute (X Y t d : Stk) : Cmd :=
  .seq (.peek 0 rH) (.seq (.loop rH Glyph.cons (distBody X Y t d)) (.pop 0 rI))

/-- body of the assembly loop: move one value to stack 0 and push a `cons` above it -/
def asmBody (Z t d : Stk) : Cmd :=
  .seq (mvVal Z 0 t d) (.seq (pushConst 0 Glyph.cons) (.peek Z rH))

/-- turn the single run on `X` back into a `cons`-chain on stack 0 -/
def assemble (X Z t d : Stk) : Cmd :=
  .seq (pushConst Z gMark)
    (.seq (.peek X rH)
      (.seq (.ite rH Glyph.cons
               (.seq (drainVals X Z t d) (.seq (.pop X rJ) (.pop X rJ)))
               (.pop X rJ))
        (.seq (pushConst 0 Glyph.nil)
          (.seq (.peek Z rH)
            (.seq (.loop rH Glyph.cons (asmBody Z t d))
              (.pop Z rJ))))))

/-- the whole sorting program -/
def sortProg (pLt pSize : Cmd) : Cmd :=
  .seq (pushConst 1 gBnd)
    (.seq (pushConst 2 gBnd)
      (.seq (pushConst 3 gBnd)
        (.seq (pushConst 4 gBnd)
          (.seq (distribute 1 2 7 8)
            (.seq (.peek 2 rF)
              (.seq (.loop rF Glyph.cons
                       (.seq (pass2 pLt pSize 1 2 3 4 5 6 10 11 12 13 7 8) (.peek 2 rF)))
                (.seq (assemble 1 9 7 8)
                  (.seq (.pop 2 rJ) (.seq (.pop 3 rJ) (.pop 4 rJ))))))))))

end Sk
end Work.Layout
