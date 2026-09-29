import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Layout.Base
import Submission.Work.Layout.Move
import Submission.Work.Layout.AA.ProgAux
import Submission.Work.SynFFT.axisKit

/-!
# `Work.SynFFT.axisLeaf`: definitions of the leaf word (blockwise transpose)

The leaf step of the blockwise transpose: given `ofList blk` with `blk.length = t*B`, produce
`stateVal ((rowsOf t B blk).map exploded)`, i.e. the `t` rows of `B` elements, each row exploded
into its `B` singleton columns, kept `int t` and `int B` below.

## The algorithm

Let `W = blk.reverse`, and let `chunk i = (rowsOf t B W).getD i []` be the `i`-th block of `B`
consecutive elements of `W` (so `chunk i` is the `(t-1-i)`-th row of `blk`, reversed).  Walking `W`
from the front and, for each element `x`, *consing* the wrapped element `.cons x .nil` onto the
current row accumulator gives, at the end of `chunk i`, the value `ofList (chunk i).reverse.map wrap`
= the `(t-1-i)`-th row of `blk` in the correct order; consing the completed rows onto the row list
gives (at the end) `ofList ((List.map RV (rowsOf t B W)).reverse)` where
`RV c = ofList (c.reverse.map wrap)`, which is exactly the required output.

The loop is driven by a binary counter `int c` on stack `stT4` (`c = B - (number of elements in the
current row)`), decremented after every element with `Work.Layout.decInt`; when the counter reaches
`0` (`Work.Layout.isZeroInt`) the completed row is moved onto the row list with
`Work.Layout.prependTo`, an empty row is pushed and the counter is reset from the template `int B`
on stack `stEl` (`Work.Layout.clearAbove` + `Work.Layout.copyIntTo`).

All working stacks carry a boundary marker `gMark` below their data; `lfPrologue` pushes the markers
and `lfEpilogue` clears the stacks back to the original contents.
-/

set_option autoImplicit false
namespace Work.SynFFT

open HvdH
open Work.Layout

/-! ## 1. Registers and stacks -/

/-- loop flag register -/
def lfF : Reg := 5
/-- peek / scratch register -/
def lfP : Reg := 6
/-- push-constant register -/
def lfQ : Reg := 7
/-- counter registers of `decInt` / `isZeroInt` / `copyIntTo` -/
def lfC1 : Reg := 9
def lfC3 : Reg := 11
def lfC4 : Reg := 12
def lfC5 : Reg := 13

/-- the remaining list `ofList W` -/
def lfStF : Stk := 1
/-- the current row accumulator (a list of wrapped elements) -/
def lfStBk : Stk := 2
/-- the list of completed rows -/
def lfStBl : Stk := 3
/-- the binary counter -/
def lfStT4 : Stk := 4
/-- `decInt` scratch -/
def lfStT2 : Stk := 5
/-- `copyIntTo` scratch -/
def lfStT5 : Stk := 6
/-- the counter template `int B` -/
def lfStEl : Stk := 7
/-- `mvVal` scratch stack (restored automatically) -/
def lfStM1 : Stk := 8
/-- `mvVal` scratch stack (restored automatically) -/
def lfStM2 : Stk := 9
/-- `mvVal` scratch stack (restored automatically) -/
def lfCA : Stk := 10
/-- `mvVal` scratch stack (restored automatically) -/
def lfCB : Stk := 11

/-- the working stacks carrying a boundary marker -/
def lfStks : List Stk :=
  [lfStF, lfStBk, lfStBl, lfStT4, lfStT2, lfStT5, lfStEl]

/-! ## 2. Pure helpers -/

/-- the wrapped element: the singleton column containing `x` -/
def lfWrap (x : Val) : Val := .cons x .nil

/-- the row value of a chunk of `W` (the reversed row of `blk`) -/
def lfRV (c : List Val) : Val := ofList (c.reverse.map lfWrap)

/-- the rows of `blk` in terms of the chunks of `W = blk.reverse`: `lfRV` of the `i`-th chunk is
the `(t-1-i)`-th row value, so the *reversed* list of the `lfRV`s is the list of row values. -/
def lfRowsVal (t B : ℕ) (W : List Val) : List Val :=
  (List.map lfRV (rowsOf t B W)).reverse

/-- The current (partial) row accumulator as a function of the processed prefix `P` of `W`: the
elements of the row processed so far, in accumulation order (i.e. reversed), wrapped into
singletons. -/
def lfRowL (B : ℕ) (P : List Val) : List Val :=
  ((P.drop ((P.length / B) * B)).reverse).map lfWrap

/-- The row list accumulator as a function of the processed prefix `P` of `W`: the completed row
values, in accumulation order (i.e. reversed). -/
def lfRowsL (t B : ℕ) (W P : List Val) : List Val :=
  (List.map lfRV ((rowsOf t B W).take (P.length / B))).reverse

/-! ## 3. Programs -/

/-- push the glyph `cst` on stack `k` -/
def lfPushS (k : Stk) (cst : Glyph) (r : Reg) : Cmd := seqs [.set r cst, .push k r]

/-- push the `nil` glyph on stack `k` -/
def lfPushNilS (k : Stk) (r : Reg) : Cmd := Work.Kernel.pushGlyphs [Glyph.nil] k r

/-- push the `cons` glyph on stack `k` -/
def lfPushConsS (k : Stk) (r : Reg) : Cmd := Work.Kernel.pushGlyphs [Glyph.cons] k r

/-- push the marker on stack `k` -/
def lfPushMarkS (k : Stk) (r : Reg) : Cmd := Work.Kernel.pushGlyphs [gMark] k r

/-- one element of the reversed block: pop the leading `cons` of `lfStF`, move the element aside,
push a `nil` on `lfStBk`, move the element above it and push two `cons` glyphs, so that the
singleton `.cons x .nil` becomes the head of the row accumulator. -/
def lfElemStep : Cmd :=
  seqs [.pop lfStF lfP, mvVal lfStF lfStM1 lfCA lfCB, lfPushNilS lfStBk lfQ,
        mvVal lfStM1 lfStBk lfCA lfCB, lfPushConsS lfStBk lfQ, lfPushConsS lfStBk lfQ]

/-- the row is complete: move the row value onto the row list, start a fresh empty row and reset the
counter from the template `int B`. -/
def lfCloseStep : Cmd :=
  seqs [prependTo lfStBk lfStBl lfCA lfCB lfP, lfPushNilS lfStBk lfQ,
        clearAbove lfStT4 lfP lfF, copyIntTo lfStEl lfStT4 lfStT5 lfC1 lfF,
        .set lfF Glyph.cons]

/-- the loop body: if the list is exhausted, stop; otherwise do one element step, decrement the
counter and, if it reaches `0`, close the row. -/
def lfBody : Cmd :=
  seqs [.peek lfStF lfP,
        .ite lfP Glyph.nil (.set lfF Glyph.eos)
          (seqs [lfElemStep, decInt lfStT4 lfStT2 lfC1 lfF lfC3 lfC4 lfC5,
                 isZeroInt lfStT4 lfC1 lfF lfC3,
                 .ite lfF Glyph.cons lfCloseStep (.set lfF Glyph.cons)])]

/-- the main loop -/
def lfLoop : Cmd := seqs [.set lfF Glyph.cons, .loop lfF Glyph.cons lfBody]

/-- push the boundary markers on all working stacks -/
def lfPrologue : Cmd := seqs (lfStks.map (fun k => lfPushMarkS k lfQ))

/-- clear all working stacks back to their original content -/
def lfEpilogue : Cmd := seqs (lfStks.map (fun k => clearTo k lfP lfF))

/-! ## 4. The cost of the loop -/

/-- Upper bound on the cost of one iteration of `lfBody` processing element `x`, with counter value
`c` and with `S` an upper bound on `Σ (vsz w)` over the wrapped elements of the current row. -/
def lfIter (B : ℕ) (x : Val) (c S : ℕ) : ℕ :=
  80 * (vsz x + 1) + 40 * (isz (c : ℤ) + 1) + 60 +
    (if c = 1 then 20 * (S + (vsz x + 2) + B + 8) + 16 * (isz (B : ℤ) + 1) + 40 else 0)

/-- Cost bound of the loop as a function of the remaining list `l`, the counter value `c` and the
row-size bound `S`. -/
def lfTC (B : ℕ) : List Val → ℕ → ℕ → ℕ
  | [], _, _ => 3
  | x :: l', c, S =>
      lfIter B x c S + lfTC B l' (if c = 1 then B else c - 1) (if c = 1 then 0 else S + (vsz x + 2))

/-- the number of row closings among the next `n` elements, when the counter starts at `c` -/
def lfCloses (B c n : ℕ) : ℕ := (n + B - c) / B

/-- Closed form of the loop cost bound: `S` bounds the accumulated row size, `c` is the counter
value, `l` the remaining list. -/
def lfCF (B S c : ℕ) (l : List Val) : ℕ :=
  80 * ((l.map (fun x => vsz x + 1)).sum) + 40 * (l.length * (isz (B : ℤ) + 1)) +
    60 * l.length + 20 * (S + (l.map (fun x => vsz x + 2)).sum) +
    20 * (lfCloses B c l.length + 1) * (B + 8) +
    16 * (lfCloses B c l.length + 1) * (isz (B : ℤ) + 1) +
    50 * (lfCloses B c l.length + 1) + 3 * (l.length + 1) + 100

end Work.SynFFT
