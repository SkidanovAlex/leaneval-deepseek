import Mathlib
import Submission.Work.Layout.AA.Defs

/-!
# `applyAlongWord`: composite programs

Concrete stack layout of the implementation (all working stacks carry their data *above* a boundary
marker `gMark`; stack 0 keeps `rest`+`R`, and receives only the current slice and the final output):

| stack | role |
|---|---|
| 0 | value stack (`rest` below, transient slice during the `q` calls) |
| 1 `sInp` | remaining input (flat array) |
| 2 `sAcc` | output accumulator (kept reversed) |
| 3 `sJobs` | DFS job stack (`cons (int C) (ofList flat)`) |
| 4 `sSl` | produced slices / later output columns |
| 5 `sOuts` | outputs of `q`, prepended |
| 6 `sCur` | current chunk / flat `F` |
| 7 `sT1` | scratch (countdown counter) |
| 8 `sT2` | scratch (reversal destination / source of the partition) |
| 9 `sCA` | group counter / scratch for `mvVal` |
| 10 `sM` | template `int m` / scratch for `mvVal` |
| 11 `sB` | template `int B` |
| 12 `sCnt` | row counter resp. chunk counter |
| 13 `sC1` | element counter resp. `C1` |
| 14 `sC2` | `C2` |
| 15 `sN` | template `int n` |

`mvVal` is always called with the fixed scratch pair `(sCA, sM)`; `mvVal` restores its scratch stacks,
so the templates survive (invariant `X 9`, `X 10` restored by every step).
-/

set_option autoImplicit false

namespace Work.Layout
namespace AA

open HvdH

def sInp : Stk := 1
def sAcc : Stk := 2
def sJobs : Stk := 3
def sSl : Stk := 4
def sOuts : Stk := 5
def sCur : Stk := 6
def sT1 : Stk := 7
def sT2 : Stk := 8
def sCA : Stk := 9
def sM : Stk := 10
def sB : Stk := 11
def sCnt : Stk := 12
def sC1 : Stk := 13
def sC2 : Stk := 14
def sN : Stk := 15

/-- remaining registers used by the counter routines -/
def rZ1 : Reg := 9
def rZ2 : Reg := 10
def rZ3 : Reg := 11
def rZ4 : Reg := 12
def rZ5 : Reg := 13

/-- push a `cons` on stack `k` -/
def pushCons (k : Stk) : Cmd := Work.Kernel.pushGlyphs [Glyph.cons] k rQ2

/-- discard a counter that has been decremented to `0` (its encoding is `[pos, iend]`). -/
def dropZero (a : Stk) : Cmd := seqs [.pop a rP, .pop a rZ1]

/-- discard the trailing `nil` of an emptied list on stack `a`. -/
def popNil (a : Stk) : Cmd := seqs [.pop a rP]

/-- take one element from the front of the list on `a` and prepend it onto the list on `b`. -/
def moveElem (a b : Stk) : Cmd :=
  seqs [.pop a rP, mvVal a b sCA sM, pushCons b]

/-- loop while the top glyph of `a` is `cons`. -/
def loopNE (a : Stk) (body : Cmd) : Cmd :=
  seqs [.peek a rP,
        .ite rP Glyph.cons (.set rF Glyph.cons) (.set rF Glyph.eos),
        .loop rF Glyph.cons
          (seqs [body, .peek a rP,
                 .ite rP Glyph.cons (.set rF Glyph.cons) (.set rF Glyph.eos)])]

/-- loop while the counter on `c` is positive: decrement it (scratch `t`) and run `body`. -/
def loopCnt (c t : Stk) (body : Cmd) : Cmd :=
  seqs [.set rF Glyph.cons,
        .loop rF Glyph.cons
          (seqs [isZeroInt c rZ1 rF rZ3,
                 .ite rF Glyph.cons (.set rF Glyph.eos)
                   (seqs [decInt c t rZ1 rF rZ3 rZ4 rZ5, body, .set rF Glyph.cons])])]

/-- one row of the block: `int B` elements moved from the input onto the chunk (reversed). -/
def chunkRow : Cmd :=
  seqs [copyIntTo sB sC1 sT1 rZ1 rZ3,
        loopCnt sC1 sT1 (moveElem sInp sCur),
        clearAbove sC1 rP rF]

/-- consume `int m` rows of `int B` elements from the input onto stack `sCur` (reversed). -/
def chunkRows : Cmd :=
  loopCnt sCnt sT1 chunkRow

/-- build the flat block for one group on `sCur`, in normal row-major order. -/
def prepBlock : Cmd :=
  seqs [pushNil sCur rQ2,
        copyIntTo sM sCnt sT1 rZ1 rZ3,
        chunkRows,
        clearAbove sCnt rP rF,
        revTo2 sCur sT2 sCA sM rP rF rQ2,
        mvVal sT2 sCur sCA sM]

/-- attach the counter `int B` to the block and push the resulting job onto the job stack. -/
def pushBlockJob : Cmd :=
  seqs [copyIntTo sB sCnt sT1 rZ1 rZ3,
        mvVal sCnt sCur sCA sM,
        pushCons sCur,
        prependTo sCur sJobs sCA sM rQ2]

/-- the input-side preparation: build the job for the current block and run the DFS. -/
def prepInput : Cmd := seqs [prepBlock, pushBlockJob]

/-- the partition of one reversed chunk: per row, first `C2` elements to `sT1`-dest,
then `C1` elements to `sCur`; the source is `sT2`. -/
def partition : Cmd :=
  loopNE sT2
    (seqs [copyIntTo sC2 sT1 sCnt rZ1 rZ3,
           loopCnt sT1 sCnt (moveElem sT2 sOuts),
           clearAbove sT1 rP rF,
           copyIntTo sC1 sT1 sCnt rZ1 rZ3,
           loopCnt sT1 sCnt (moveElem sT2 sCur),
           clearAbove sT1 rP rF])

/-- split the current chunk (counter on `sCnt`, flat on `sCur`): produce `C1`, `C2`, partition and
push the two sub-jobs (the second on top). -/
def splitChunk : Cmd :=
  seqs [copyIntTo sCnt sC1 sT1 rZ1 rZ3,
        halveInt sC1 rZ1 rZ2,
        copyIntTo sCnt sC2 sT1 rZ1 rZ3,
        incInt sC2 sT1 rZ1 rZ2 rZ3 rZ4,
        halveInt sC2 rZ1 rZ2,
        clearAbove sCnt rP rF,
        revTo2 sCur sT2 sCA sM rP rF rQ2,
        pushNil sCur rQ2,
        pushNil sOuts rQ2,
        partition,
        mvVal sC1 sCur sCA sM, pushCons sCur,
        prependTo sCur sJobs sCA sM rQ2,
        mvVal sC2 sOuts sCA sM, pushCons sOuts,
        prependTo sOuts sJobs sCA sM rQ2]

/-- the DFS: while the job stack is non-empty, take a job apart and either emit the column (counter
`1`), discard it (counter `0`) or split it. -/
def dfsLoop : Cmd :=
  loopNE sJobs
    (seqs [.pop sJobs rP, mvVal sJobs sCur sCA sM,
           .pop sCur rP, mvVal sCur sCnt sCA sM,
           isZeroInt sCnt rZ1 rZ2 rZ3,
           .ite rZ2 Glyph.cons (clearAbove sCur rP rF)
             (seqs [isOneInt sCnt rZ1 rZ2 rZ3 rZ4,
                    .ite rZ2 Glyph.cons (prependTo sCur sSl sCA sM rQ2)
                      splitChunk])])

/-- run `q` on every slice of `sSl` (in order), collecting the outputs on `sOuts` (prepended). -/
def qLoop (q : Cmd) : Cmd :=
  seqs [pushNil sOuts rQ2,
  loopNE sSl
    (seqs [.pop sSl rP, mvVal sSl 0 sCA sM,
           q,
           mvVal 0 sOuts sCA sM, pushCons sOuts])]

/-- concatenate the outputs of `sOuts` (popped in reverse order) into the flat list `F` on `sCur`. -/
def buildF : Cmd :=
  seqs [pushNil sCur rQ2,
        loopNE sOuts
          (seqs [.pop sOuts rP, mvVal sOuts sT1 sCA sM,
                 revTo2 sT1 sT2 sCA sM rP rF rQ2,
                 loopNE sT2 (moveElem sT2 sCur),
                 clearAbove sT2 rP rF]),
        clearAbove sOuts rP rF]

/-- attach the counter `int n` to `F` and push it as a job. -/
def pushFJob : Cmd :=
  seqs [copyIntTo sN sCnt sT1 rZ1 rZ3,
        mvVal sCnt sCur sCA sM,
        pushCons sCur,
        prependTo sCur sJobs sCA sM rQ2]

/-- prepend the elements of every column of `sSl` (in order) onto the accumulator `sAcc`. -/
def accumulate : Cmd :=
  loopNE sSl
    (seqs [.pop sSl rP, mvVal sSl sT1 sCA sM,
           loopNE sT1 (moveElem sT1 sAcc),
           clearAbove sT1 rP rF])

/-- one group: block, transpose, `q` on the slices, transpose back, accumulate. -/
def groupBody (q : Cmd) : Cmd :=
  seqs [prepInput, dfsLoop, qLoop q, buildF, pushFJob, dfsLoop, accumulate]

/-- push the boundary marker on every working stack. -/
def prologue : Cmd :=
  seqs (([.push sInp rP, .push sAcc rP, .push sJobs rP, .push sSl rP, .push sOuts rP,
          .push sCur rP, .push sT1 rP, .push sT2 rP, .push sCA rP, .push sM rP,
          .push sB rP, .push sCnt rP, .push sC1 rP, .push sC2 rP, .push sN rP] : List Cmd).map
        (fun c => seqs [.set rP gMark, c]))

/-- clear every working stack down to its boundary marker (and pop the marker). -/
def epilogue : Cmd :=
  seqs [clearTo sInp rP rF, clearTo sAcc rP rF, clearTo sJobs rP rF, clearTo sSl rP rF,
        clearTo sOuts rP rF, clearTo sCur rP rF, clearTo sT1 rP rF, clearTo sT2 rP rF,
        clearTo sCA rP rF, clearTo sM rP rF, clearTo sB rP rF, clearTo sCnt rP rF,
        clearTo sC1 rP rF, clearTo sC2 rP rF, clearTo sN rP rF]

/-- move `int A`, `int m`, `int n`, `int B` and the input list off stack 0 onto their stacks. -/
def unpack : Cmd :=
  seqs [mvVal 0 sCA sT1 sT2, mvVal 0 sM sT1 sT2, mvVal 0 sN sT1 sT2, mvVal 0 sB sT1 sT2,
        mvVal 0 sInp sT1 sT2,
        pushNil sAcc rQ2, pushNil sJobs rQ2, pushNil sSl rQ2]

/-- reverse the accumulator and put it on top of stack 0 (above `rest`). -/
def finish : Cmd := seqs [revTo2 sAcc sT2 sCA sM rP rF rQ2, mvVal sT2 0 sCA sM]

/-- the whole program. -/
def prog (q : Cmd) : Cmd :=
  seqs [prologue, unpack,
        isZeroInt sB rZ1 rZ2 rZ3,
        .ite rZ2 Glyph.cons finish
          (seqs [loopCnt sCA sT1 (groupBody q), finish]),
        epilogue]

end AA
end Work.Layout
