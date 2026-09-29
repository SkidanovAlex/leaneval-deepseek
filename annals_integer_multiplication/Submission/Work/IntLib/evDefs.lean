import Mathlib
import Submission.Work.IntLib.chunkDefs
import Submission.Work.IntLib.chunkProg
import Submission.Work.IntLib.Basic
import Submission.Work.IntLib.ofBitsAPI
import Submission.Work.IntLib.Shift.Base
import Submission.Work.Layout.Base

/-!
# `IntLib` / `evalPoly`: definitions

The `evalPoly` word reads a `cons`-chain `intList hs` of `m` naturals (each `< 2^(3b)`) off stack 0
and replaces it by the single value `int (Σ_j hs[j]·2^(b·j))`.

The algorithm is a streaming "window" addition: the digits overlap, so the low bits of the result
can only be finalised after all digits contributing to them have been seen.  Keeping

* the *window* `W` (`aW`, bits stored least-significant-on-top) = the part of the partial sum
  `S_j = Σ_{i<j} hs[i]·2^(b·i)` above position `b·j`, and
* the *output* `LO` (`aO`, bits in increasing significance order, preceded by the sign `pos`),

the step for one digit `h` is: add `h` at the bottom of the window (ripple carry), then move exactly
`b` bits of the result to the output.  The invariant after `j` steps is
`ofBits LO + 2^(LO.length) * ofBits W = evalChunks (hs.take j) b` with `LO.length = b*j` and
`W.length ≤ 3*b + 1`.

Stack allocation:

| stack | role |
|---|---|
| `aC = 0`  | the `cons`-chain (the input / remaining digits) |
| `aW = 1`  | the window |
| `aA = 2`  | scratch: the glyphs of the digit being read (reversed) |
| `aO = 3`  | the finalised low bits |
| `aB = 4`  | scratch: the bits of the digit in order / the carry-add buffer |
| `a2 = 5`  | scratch: second carry-add buffer |
| `aCB = 6` | master counter `Unary b` |
| `aCW = 7` | working counter (refilled from `aCB` for every digit) |
| `aL = 8`  | buffer for the whole chain while `b` is being read |
| `aR = 9`  | the reversed encoding of `int b` (input of `UR.urProg`) |
| `aT = 10` | `UR` temp |
| `aV = 11` | `UR` target (the rebuilt `int b`, unused) |
-/

set_option autoImplicit false

namespace Work.IntLib

open HvdH
open Work.Layout

/-! ## Stacks, registers, flags -/

def aC : Stk := 0
def aW : Stk := 1
def aA : Stk := 2
def aO : Stk := 3
def aB : Stk := 4
def a2 : Stk := 5
def aCB : Stk := 6
def aCW : Stk := 7
def aL : Stk := 8
def aR : Stk := 9
def aT : Stk := 10
def aV : Stk := 11

/-- loop-continue flag of the `evalPoly` loops -/
def fGo : Glyph := .mk 15
/-- loop-stop flag -/
def fStop : Glyph := .mk 12

theorem fGo_ne_fStop : fGo ≠ fStop := by decide
theorem fGo_ne_gTok : fGo ≠ gTok := by decide
theorem fStop_ne_gTok : fStop ≠ gTok := by decide
theorem fGo_ne_gEnd : fGo ≠ gEnd := by decide
theorem fStop_ne_gEnd : fStop ≠ gEnd := by decide
theorem fGo_ne_pos : fGo ≠ Glyph.pos := by decide
theorem fStop_ne_pos : fStop ≠ Glyph.pos := by decide
theorem fGo_ne_iend : fGo ≠ Glyph.iend := by decide
theorem fStop_ne_iend : fStop ≠ Glyph.iend := by decide
theorem fGo_ne_cons : fGo ≠ Glyph.cons := by decide
theorem fStop_ne_cons : fStop ≠ Glyph.cons := by decide
theorem fGo_ne_nil : fGo ≠ Glyph.nil := by decide
theorem fStop_ne_nil : fStop ≠ Glyph.nil := by decide

/-- loop register of the `evalPoly` loops -/
def rLp : Reg := (0 : Fin 16)
/-- first scratch register -/
def rX : Reg := (1 : Fin 16)
/-- second scratch register -/
def rY : Reg := (2 : Fin 16)

/-! ## The state function and the invariant -/

/-- The stack function of the `evalPoly` word after `j` processed digits: the remaining chain on
`aC`, the window `W` on `aW` (least significant bit on top), the finalised bits `LO` (increasing
significance order, below the sign `pos`) on `aO`, an empty working counter, and the master counter;
`Y` is the content below the data of every stack. -/
def evStk (hs : List ℕ) (b j : ℕ) (W LO : List Bool) (Y : Stk → List Glyph) : Stk → List Glyph :=
  fun k =>
    if k = aC then Val.enc (intList (hs.drop j)) ++ Y aC
    else if k = aW then W.map Glyph.bit ++ Shift.gmk aW :: Y aW
    else if k = aO then LO.reverse.map Glyph.bit ++ [Glyph.pos] ++ Shift.gmk aO :: Y aO
    else if k = aCW then Unary 0 (Shift.gmk aCW :: Y aCW)
    else if k = aCB then Unary b (Shift.gmk aCB :: Y aCB)
    else if k = aA then Shift.gmk aA :: Y aA
    else if k = aB then Shift.gmk aB :: Y aB
    else if k = a2 then Shift.gmk a2 :: Y a2
    else if k = aL then Shift.gmk aL :: Y aL
    else Y k

/-- The arithmetic part of the invariant. -/
def evVal (hs : List ℕ) (b j : ℕ) (W LO : List Bool) : Prop :=
  LO.length = b * j ∧ W.length ≤ 3 * b + 1 ∧
    ofBits LO + 2 ^ LO.length * ofBits W = evalChunks (hs.take j) b

@[simp] theorem evStk_aC (hs : List ℕ) (b j : ℕ) (W LO : List Bool) (Y : Stk → List Glyph) :
    evStk hs b j W LO Y aC = Val.enc (intList (hs.drop j)) ++ Y aC := by
  simp only [evStk, if_pos rfl, ↓reduceIte]

@[simp] theorem evStk_aW (hs : List ℕ) (b j : ℕ) (W LO : List Bool) (Y : Stk → List Glyph) :
    evStk hs b j W LO Y aW = W.map Glyph.bit ++ Shift.gmk aW :: Y aW := by
  have h : ¬ (aW = aC) := by decide
  simp only [evStk, if_neg h, if_pos rfl, ↓reduceIte]

@[simp] theorem evStk_aO (hs : List ℕ) (b j : ℕ) (W LO : List Bool) (Y : Stk → List Glyph) :
    evStk hs b j W LO Y aO = LO.reverse.map Glyph.bit ++ [Glyph.pos] ++ Shift.gmk aO :: Y aO := by
  have h1 : ¬ (aO = aC) := by decide
  have h2 : ¬ (aO = aW) := by decide
  simp only [evStk, if_neg h1, if_neg h2, if_pos rfl, ↓reduceIte]

@[simp] theorem evStk_aCW (hs : List ℕ) (b j : ℕ) (W LO : List Bool) (Y : Stk → List Glyph) :
    evStk hs b j W LO Y aCW = Unary 0 (Shift.gmk aCW :: Y aCW) := by
  have h1 : ¬ (aCW = aC) := by decide
  have h2 : ¬ (aCW = aW) := by decide
  have h3 : ¬ (aCW = aO) := by decide
  simp only [evStk, if_neg h1, if_neg h2, if_neg h3, if_pos rfl, ↓reduceIte]

@[simp] theorem evStk_aCB (hs : List ℕ) (b j : ℕ) (W LO : List Bool) (Y : Stk → List Glyph) :
    evStk hs b j W LO Y aCB = Unary b (Shift.gmk aCB :: Y aCB) := by
  have h1 : ¬ (aCB = aC) := by decide
  have h2 : ¬ (aCB = aW) := by decide
  have h3 : ¬ (aCB = aO) := by decide
  have h4 : ¬ (aCB = aCW) := by decide
  simp only [evStk, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos rfl, ↓reduceIte]

theorem evStk_other (hs : List ℕ) (b j : ℕ) (W LO : List Bool) (Y : Stk → List Glyph) {k : Stk}
    (h1 : k ≠ aC) (h2 : k ≠ aW) (h3 : k ≠ aO) (h4 : k ≠ aCW) (h5 : k ≠ aCB) (h6 : k ≠ aA)
    (h7 : k ≠ aB) (h8 : k ≠ a2) (h9 : k ≠ aL) :
    evStk hs b j W LO Y k = Y k := by
  simp only [evStk, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7,
    if_neg h8, if_neg h9, ↓reduceIte]

@[simp] theorem evStk_aA (hs : List ℕ) (b j : ℕ) (W LO : List Bool) (Y : Stk → List Glyph) :
    evStk hs b j W LO Y aA = Shift.gmk aA :: Y aA := by
  simp only [evStk, if_neg (by decide : ¬ (aA = aC)), if_neg (by decide : ¬ (aA = aW)),
    if_neg (by decide : ¬ (aA = aO)), if_neg (by decide : ¬ (aA = aCW)),
    if_neg (by decide : ¬ (aA = aCB)), if_pos (by decide : aA = aA), ↓reduceIte]

@[simp] theorem evStk_aB (hs : List ℕ) (b j : ℕ) (W LO : List Bool) (Y : Stk → List Glyph) :
    evStk hs b j W LO Y aB = Shift.gmk aB :: Y aB := by
  simp only [evStk, if_neg (by decide : ¬ (aB = aC)), if_neg (by decide : ¬ (aB = aW)),
    if_neg (by decide : ¬ (aB = aO)), if_neg (by decide : ¬ (aB = aCW)),
    if_neg (by decide : ¬ (aB = aCB)), if_neg (by decide : ¬ (aB = aA)),
    if_pos (by decide : aB = aB), ↓reduceIte]

@[simp] theorem evStk_a2 (hs : List ℕ) (b j : ℕ) (W LO : List Bool) (Y : Stk → List Glyph) :
    evStk hs b j W LO Y a2 = Shift.gmk a2 :: Y a2 := by
  simp only [evStk, if_neg (by decide : ¬ (a2 = aC)), if_neg (by decide : ¬ (a2 = aW)),
    if_neg (by decide : ¬ (a2 = aO)), if_neg (by decide : ¬ (a2 = aCW)),
    if_neg (by decide : ¬ (a2 = aCB)), if_neg (by decide : ¬ (a2 = aA)),
    if_neg (by decide : ¬ (a2 = aB)), if_pos (by decide : a2 = a2), ↓reduceIte]

@[simp] theorem evStk_aL (hs : List ℕ) (b j : ℕ) (W LO : List Bool) (Y : Stk → List Glyph) :
    evStk hs b j W LO Y aL = Shift.gmk aL :: Y aL := by
  simp only [evStk, if_neg (by decide : ¬ (aL = aC)), if_neg (by decide : ¬ (aL = aW)),
    if_neg (by decide : ¬ (aL = aO)), if_neg (by decide : ¬ (aL = aCW)),
    if_neg (by decide : ¬ (aL = aCB)), if_neg (by decide : ¬ (aL = aA)),
    if_neg (by decide : ¬ (aL = aB)), if_neg (by decide : ¬ (aL = a2)),
    if_pos (by decide : aL = aL), ↓reduceIte]

/-! ## The loop programs -/

/-- The body of the `evalPoly` main loop: consume one `cons` cell of the chain, read the digit with
`readG`, refill the working counter with `copyG`, add the digit with `addG`, and decide (from the
next glyph of the chain) whether to continue. -/
def evBody (readG copyG addG : Cmd) : Cmd :=
  seqs [.pop aC rX, readG, copyG, addG, .peek aC rY,
    .ite rY Glyph.cons (.set rLp fGo) (.set rLp fStop)]

/-- The main loop of the `evalPoly` word. -/
def evLoopP (readG copyG addG : Cmd) : Cmd :=
  seqs [.set rLp fGo, .loop rLp fGo (evBody readG copyG addG)]

end Work.IntLib
