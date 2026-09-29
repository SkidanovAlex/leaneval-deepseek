import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Layout.AA.PureDefs
import Submission.Work.Layout.AA.rowsOf_facts
import Submission.Work.Layout.AA.ProgAux
import Submission.Work.Layout.Base
import Submission.Work.Layout.Move
import Submission.Work.Layout.AA.Defs
import Submission.Work.Kernel.Raw

/-!
# `pbApplyAlong`: a flat-array `applyAlong` word (paper Lemma 2.11) — definitions

Pure list layer and StackLang programs of a self-contained implementation of
`HvdH.LayoutLib.applyAlong` for the flat `A × m × B` layout of `HvdH.slices`.

## The algorithm (per group `a < A`)

* `exBlock`: pop the next `m*B` elements off the input list `sInp`, *prepending* them on the scratch
  stack `sBk`: it holds the group's `m × B` block, **reversed**;
* `trProg` (used twice): given a reversed flat `M × C` array (on stack 0, above `int M :: int C`)
  and the counters `M`, `C`, produce the `C` columns of the array, in order, as one list value;
  * `trChunk`: chop the reversed list into `M` rows of `C` elements and wrap each element into a
    singleton column — the *level-0 block list* (`lv0`);
  * `trLevelLoop`: repeat the pairing pass `trPass`: merge adjacent blocks with `zwP` (the Kernel
    `zipWith` word with the Layout `append` word as operation) until a single block remains;
* `mapP q` (`Work.Kernel.mapList`) applies `q` to every slice;
* `flatP` (`Work.Layout.flattenWord`) concatenates the outputs into the flat `B × n` matrix `F`
  (the flatten word leaves its input below the output; it is dropped with `dropP`);
* `revP`, then `trProg` again (counters `B`, `n`): the `n` columns of `F`;
* `mapP revP` reverses each column; `foldP` (with `pushConsS 0`) prepends them onto the accumulator
  `sAcc`; finally `revP` reverses `sAcc` onto stack 0.

Every internal working stack carries a boundary marker `gMark` pushed by the prologue and removed by
the epilogue (`clearTo`); all data above a marker is built from `Val` encodings and `nil`/`cons`
glyphs, hence contains no marker (`MFree`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Work.Resample.PB

open HvdH
open Work.Layout

/-! ## 1. Pure layer -/

open Work.Layout.AA

/-- elementwise concatenation of two blocks (a block is a list of columns). -/
def mergeBlk (a b : List (List Val)) : List (List Val) :=
  List.zipWith (fun x y => x ++ y) a b

/-- One level step of the group decomposition: pair adjacent groups (leftover last).  A *group* is a
list of rows, so a group list is a `List (List (List Val))`. -/
def grpStep : List (List (List Val)) → List (List (List Val))
  | [] => []
  | [g] => [g]
  | g1 :: g2 :: rest => (g1 ++ g2) :: grpStep rest

/-- `k` level steps of the group decomposition. -/
def grpIter : ℕ → List (List (List Val)) → List (List (List Val))
  | 0, gs => gs
  | k + 1, gs => grpIter k (grpStep gs)

/-- The block of a group of rows: the columns of the group's flattened rows. -/
def grpBlk (C : ℕ) (g : List (List Val)) : List (List Val) := colsOf g.length C g.flatten

/-- The block list of a group list.  A block is a list of columns. -/
def blksOf (C : ℕ) (gs : List (List (List Val))) : List (List (List Val)) := gs.map (grpBlk C)

/-- One level step of the block list: merge adjacent blocks (leftover last). -/
def lvlStep : List (List (List Val)) → List (List (List Val))
  | [] => []
  | [b] => [b]
  | b1 :: b2 :: rest => mergeBlk b1 b2 :: lvlStep rest

/-- `k` level steps of the block list. -/
def lvlIter : ℕ → List (List (List Val)) → List (List (List Val))
  | 0, bs => bs
  | k + 1, bs => lvlIter k (lvlStep bs)

/-- The `Val` of a block (a list of column values). -/
def blkVal (b : List (List Val)) : Val := ofList (b.map ofList)

/-- The `Val` of a block list. -/
def blksVal (bs : List (List (List Val))) : Val := ofList (bs.map blkVal)

/-- The level-0 block list of the flat array `L`: every row wrapped into singleton columns. -/
def lv0 (M C : ℕ) (L : List Val) : List (List (List Val)) :=
  (rowsOf M C L).map (fun r => r.map (fun e => [e]))

/-- The level-0 *group* list of the flat array `L`: every row is its own group. -/
def gs0 (M C : ℕ) (L : List Val) : List (List (List Val)) :=
  (rowsOf M C L).map (fun r => [r])

/-! ## 2. Registers and stacks -/

/-- loop-flag register -/
def rL : Reg := 5
/-- peek register -/
def rPz : Reg := 6
/-- push-constant register -/
def rQz : Reg := 7
/-- scratch register -/
def rTz : Reg := 8
/-- registers of the counter routines (distinct, and avoiding 5..8) -/
def rC1 : Reg := 9
def rC2 : Reg := 10
def rC3 : Reg := 11
def rC4 : Reg := 12
def rC5 : Reg := 13

/-- internal stacks of `trProg` -/
def tBl : Stk := 1   --! block list (level representation)
def tBk : Stk := 2   --! current block / a popped block
def tF : Stk := 3    --! the reversed flat input
def tOut : Stk := 4  --! the pass output (kept reversed)
def tRt : Stk := 5   --! template `int M`
def tEl : Stk := 6   --! template `int C`
def tA : Stk := 7    --! second popped block / element scratch
def tT1 : Stk := 8   --! loop counter
def tT2 : Stk := 9   --! scratch (decInt)
def tT3 : Stk := 10  --! scratch (mvVal)
def tT4 : Stk := 11  --! loop counter
def tT5 : Stk := 12  --! scratch (copyIntTo)

/-- all internal stacks of the transpose -/
def trStks : List Stk := [tBl, tBk, tF, tOut, tRt, tEl, tA, tT1, tT2, tT3, tT4, tT5]

/-! ## 3. Elementary programs -/

/-- `pushConstS k c r`: push the glyph `c` on stack `k` (via register `r`). -/
def pushConstS (k : Stk) (c : Glyph) (r : Reg) : Cmd := seqs [.set r c, .push k r]

/-- push the boundary marker `gMark` on stack `k`. -/
def pushMarkS (k : Stk) (r : Reg) : Cmd := pushConstS k gMark r

/-- push the empty list `nil` on stack `k`. -/
def pushNilS (k : Stk) (r : Reg) : Cmd := Work.Kernel.pushGlyphs [Glyph.nil] k r

/-- push a `cons` glyph on stack `k`. -/
def pushConsS (k : Stk) (r : Reg) : Cmd := Work.Kernel.pushGlyphs [Glyph.cons] k r

/-- `cntLoop c t body`: while the counter on `c` is positive, decrement it and run `body`
(the body must re-set the flag `rL` to `cons`). -/
def cntLoop (c t : Stk) (body : Cmd) : Cmd :=
  seqs [.set rL Glyph.cons,
        .loop rL Glyph.cons
          (seqs [isZeroInt c rC1 rL rC3,
                 .ite rL Glyph.cons (.set rL Glyph.eos)
                   (seqs [decInt c t rC1 rL rC3 rC4 rC5, body, .set rL Glyph.cons])])]

/-! ## 4. The transpose -/

/-- the prologue: a boundary marker on every internal stack -/
def trPrologue : Cmd := seqs (trStks.map (fun k => pushMarkS k rQz))

/-- the epilogue: strip every internal stack down to (and including) its marker -/
def trEpilogue : Cmd := seqs (trStks.map (fun k => clearTo k rPz rL))

/-- move `int M`, `int C` and the reversed flat input list from stack 0 to their stacks -/
def trSetup : Cmd :=
  seqs [mvVal 0 tRt tT2 tT3, mvVal 0 tEl tT2 tT3, mvVal 0 tF tT2 tT3]

/-- one element of the reversed flat list (`tF`) wrapped into a singleton column prepended to `tBk` -/
def trChunkEl : Cmd :=
  seqs [.pop tF rPz, mvVal tF tA tT2 tT3, pushConstS tBk Glyph.nil rQz, mvVal tA tBk tT2 tT3,
        pushConsS tBk rQz, pushConsS tBk rQz]

/-- one row of the chunking: `C` wrapped elements, then the block is prepended to the block list -/
def trChunkRow : Cmd :=
  seqs [pushNilS tBk rQz,
        copyIntTo tEl tT4 tT5 rC1 rL,
        cntLoop tT4 tT2 (seqs [trChunkEl, .set rL Glyph.cons]),
        clearAbove tT4 rPz rL,
        prependTo tBk tBl tT2 tT3 rPz]

/-- the chunking: `tF` holds the reversed flat list; build the level-0 block list on `tBl` -/
def trChunk : Cmd :=
  seqs [pushNilS tBl rQz,
        copyIntTo tRt tT1 tT5 rC1 rL,
        cntLoop tT1 tT2 (seqs [trChunkRow, .set rL Glyph.cons]),
        clearAbove tT1 rPz rL,
        clearAbove tF rPz rL]

/-- one pairing step of the pass: pop two blocks of `tBl`, merge them with `zwP`, prepend the result
to `tOut` (or carry a single leftover block and set the flag to `eos`). -/
def trPassBody (zwP : Cmd) : Cmd :=
  seqs [.pop tBl rPz,
        mvVal tBl tBk tT2 tT3,
        .peek tBl rPz,
        .ite rPz Glyph.cons
          (seqs [.pop tBl rPz,
                 mvVal tBl tA tT2 tT3,
                 mvVal tA 0 tT2 tT3,
                 mvVal tBk 0 tT2 tT3,
                 zwP,
                 prependTo 0 tOut tT2 tT3 rPz,
                 .peek tBl rPz,
                 .ite rPz Glyph.cons (.set rL Glyph.cons) (.set rL Glyph.eos)])
          (seqs [prependTo tBk tOut tT2 tT3 rPz, .set rL Glyph.eos])]

/-- the pairing pass: while `tBl` is non-empty, pair up its blocks -/
def trPass (zwP : Cmd) : Cmd :=
  seqs [pushNilS tOut rQz, .set rL Glyph.cons, .loop rL Glyph.cons (trPassBody zwP)]

/-- The exit test of `trLevelLoop`: sets `rL` to `cons` iff the block list `tBl` holds at least two
blocks.  The first block is moved aside with `mvVal` before the second `peek`, otherwise the peek
would inspect the head of the first block (a `cons` whenever the block is non-empty). -/
def trTestTwo : Cmd :=
  seqs [.peek tBl rPz,
        .ite rPz Glyph.cons
          (seqs [.pop tBl rPz,
                 mvVal tBl tA tT2 tT3,
                 .peek tBl rPz,
                 .ite rPz Glyph.cons
                   (seqs [mvVal tA tBl tT2 tT3, pushConsS tBl rQz, .set rL Glyph.cons])
                   (seqs [mvVal tA tBl tT2 tT3, pushConsS tBl rQz, .set rL Glyph.eos])])
          (.set rL Glyph.eos)]

/-- the level loop: while the block list has at least two blocks, run one pairing pass, reverse the
result back onto `tBl`, and test again -/
def trLevelLoop (zwP revP : Cmd) : Cmd :=
  seqs [.set rL Glyph.cons,
        .loop rL Glyph.cons
          (seqs [trPass zwP,
                 clearAbove tBl rPz rL,
                 mvVal tOut 0 tT2 tT3,
                 revP,
                 mvVal 0 tBl tT2 tT3,
                 trTestTwo])]

/-- the cleanup: the block list holds one block; expose it on stack 0 -/
def trFinish : Cmd := seqs [.pop tBl rPz, mvVal tBl 0 tT2 tT3, clearAbove tBl rPz rL]

/-- **The transpose**: reversed flat `M × C` array (on stack 0, above `int M :: int C`) to the list
of its `C` columns (in order). -/
def trProg (zwP revP : Cmd) : Cmd :=
  seqs [trPrologue, trSetup, trChunk, trLevelLoop zwP revP, trFinish, trEpilogue]

/-! ## 5. The main program -/

/-- stacks of the main program -/
def sInp : Stk := 1   --! the remaining input (flat `es`)
def sAcc : Stk := 2   --! the accumulator (kept reversed)
def sBk : Stk := 3    --! the reversed block of the current group
def sSl : Stk := 4    --! a list of column values
def sO : Stk := 5     --! a parked value
def sT1 : Stk := 6
def sT2 : Stk := 7
def sA : Stk := 8     --! template `int A`
def sM : Stk := 9     --! template `int m`
def sN : Stk := 10    --! template `int n`
def sB : Stk := 11    --! template `int B`
def sT6 : Stk := 12
def sT3 : Stk := 13
def sT4 : Stk := 14
def sT5 : Stk := 15

/-- all main-program stacks -/
def mnStks : List Stk := [sInp, sAcc, sBk, sSl, sO, sT1, sT2, sA, sM, sN, sB, sT6, sT3, sT4, sT5]

/-- the prologue of the main program -/
def mnPrologue : Cmd := seqs (mnStks.map (fun k => pushMarkS k rQz))

/-- the epilogue of the main program -/
def mnEpilogue : Cmd := seqs (mnStks.map (fun k => clearTo k rPz rL))

/-- pop the four counters and the input list off stack 0, initialise the accumulator -/
def mnSetup : Cmd :=
  seqs [mvVal 0 sA sT4 sT5, mvVal 0 sM sT4 sT5, mvVal 0 sN sT4 sT5, mvVal 0 sB sT4 sT5,
        mvVal 0 sInp sT4 sT5, pushNilS sAcc rQz]

/-- one element of the input moved (prepended) to the block stack -/
def exEl : Cmd := seqs [.pop sInp rPz, mvVal sInp sBk sT4 sT5, pushConsS sBk rQz]

/-- one row of the group block: `B` elements of `sInp` prepended to `sBk` -/
def exRow : Cmd :=
  seqs [copyIntTo sB sT6 sT3 rC1 rL,
        cntLoop sT6 sT2 (seqs [exEl, .set rL Glyph.cons]),
        clearAbove sT6 rPz rL]

/-- extract the block of the current group: `m` rows of `B` elements, prepended on `sBk` -/
def exBlock : Cmd :=
  seqs [pushNilS sBk rQz,
        copyIntTo sM sT1 sT3 rC1 rL,
        cntLoop sT1 sT2 (seqs [exRow, .set rL Glyph.cons]),
        clearAbove sT1 rPz rL]

/-- push copies of the counters `c2` then `c1` on stack 0 (so that stack 0 becomes
`int c1 :: int c2 :: rest`) -/
def pushCounters (c1 c2 : Stk) : Cmd :=
  seqs [copyIntTo c2 sT6 sT3 rC1 rL, mvVal sT6 0 sT4 sT5,
        copyIntTo c1 sT6 sT3 rC1 rL, mvVal sT6 0 sT4 sT5]

/-- run the transpose on the reversed block of `sBk` and park the result on `sSl` -/
def trOfBlock (zwP revP : Cmd) : Cmd :=
  seqs [mvVal sBk 0 sT4 sT5, pushCounters sM sB, trProg zwP revP, mvVal 0 sSl sT4 sT5]

/-- the group body -/
def grpBody (zwP revP flatP dropP : Cmd) (mapP foldP : Cmd → Cmd) (q : Cmd) : Cmd :=
  seqs [exBlock,
        trOfBlock zwP revP,
        mvVal sSl 0 sT4 sT5, mapP q, mvVal 0 sSl sT4 sT5,
        mvVal sSl 0 sT4 sT5, flatP, mvVal 0 sO sT4 sT5, dropP, mvVal sO 0 sT4 sT5,
        revP,
        pushCounters sB sN,
        trProg zwP revP,
        mapP revP,
        mvVal 0 sSl sT4 sT5,
        mvVal sAcc 0 sT4 sT5,
        mvVal sSl 0 sT4 sT5,
        foldP (pushConsS 0 rQz),
        mvVal 0 sAcc sT4 sT5]

/-- the whole main program -/
def mainProg (zwP revP flatP dropP : Cmd) (mapP foldP : Cmd → Cmd) (q : Cmd) : Cmd :=
  seqs [mnPrologue, mnSetup,
        cntLoop sA sT2 (seqs [grpBody zwP revP flatP dropP mapP foldP q, .set rL Glyph.cons]),
        clearAbove sA rPz rL,
        mvVal sAcc 0 sT4 sT5, revP,
        mnEpilogue]

end Work.Resample.PB
