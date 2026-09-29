import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Layout.Base
import Submission.Work.Layout.Move
import Submission.Work.ConvR.basic

set_option autoImplicit false

/-!
# `ztabProd`: shared vocabulary

Definitions for the word `Work.Transform.ztabProd` (the "product of a list of naturals, skipping
the 1's" word of the `Transform` area).

## The algorithm

The value stack is `intList ts :: rest`.  The word

1. `dup`s the list (so that one copy is consumed, one is kept for the output),
2. pushes the marker `zM` on stack `1` and moves the *consumed* copy of the list onto stack `1`
   (`Layout.mvVal`), so `stack 1 = encLN ts ++ zM :: old stack 1`,
3. pushes the accumulator `int 1` on stack `0` (so `stack 0 = encs (int 1 :: intList ts :: rest)`),
4. walks `stack 1` element by element (`zBody`): pop the `cons` glyph, `mvVal` the element
   `int t` onto `stack 0` (on top of the accumulator), test whether `t = 1` by looking at the
   first three glyphs `pos`, `bit true`, `iend` of its encoding, multiply (`mulS`) only if
   `t ≠ 1`, and finally pop the `nil` that terminates the copy,
5. pops the marker `zM` again, restoring stack `1`.

The cost is `O(vsz (intList ts) + ts.prod * p ^ 2)`: the per-element overhead is
`O(isz t)` (`mvVal` + a constant), the multiplication is paid only for the elements `t ≥ 2`, and
one shows `Σ_{t ≥ 2} isz t ≤ 4B`, `isz (Π_{t ≥ 2} t) ≤ 2B + 2` where `B = Σ_{t ≥ 2} (t.size - 1)`,
while `ts.prod ≥ 2^B`.
-/

namespace Work.Transform

open HvdH

/-! ## Glyphs, registers, the encoded list -/

/-- Marker put on the scratch stack `1` below the copy of the list. -/
def zM : Glyph := .mk 11

/-- Flag: run one more iteration of the walk. -/
def zCont : Glyph := .mk 12

/-- Flag: the walk is over. -/
def zStop : Glyph := .mk 13

@[simp] theorem zM_ne_nil : zM ≠ Glyph.nil := by decide
@[simp] theorem zM_ne_cons : zM ≠ Glyph.cons := by decide
@[simp] theorem zM_ne_iend : zM ≠ Glyph.iend := by decide
theorem zM_ne_pos : zM ≠ Glyph.pos := by decide
theorem zM_ne_bit (b : Bool) : zM ≠ Glyph.bit b := fun h => by cases h
@[simp] theorem znil_ne_zM : Glyph.nil ≠ zM := fun h => zM_ne_nil h.symm
@[simp] theorem znil_ne_zCont : Glyph.nil ≠ zCont := by decide
@[simp] theorem znil_ne_zStop : Glyph.nil ≠ zStop := by decide
@[simp] theorem zcons_ne_nil : Glyph.cons ≠ Glyph.nil := by decide
@[simp] theorem zCont_ne_zStop : zCont ≠ zStop := by decide
@[simp] theorem zStop_ne_zCont : zStop ≠ zCont := by decide

/-- head glyph of the scratch stack -/
def rZH : Reg := 1
/-- scratch register -/
def rZX : Reg := 2
/-- first popped glyph of the element -/
def rZA : Reg := 3
/-- second popped glyph of the element -/
def rZB : Reg := 4
/-- third (peeked) glyph of the element -/
def rZC : Reg := 5
/-- loop register -/
def rZL : Reg := 6

/-- `encLN ts` is the encoding of the list value `intList ts`: a `cons` for each element and a
final `nil`. -/
def encLN : List ℕ → List Glyph
  | [] => [Glyph.nil]
  | t :: ts => Glyph.cons :: ((Val.int (t : ℤ)).enc ++ encLN ts)

@[simp] theorem encLN_nil : encLN [] = [Glyph.nil] := rfl

theorem encLN_cons (t : ℕ) (ts : List ℕ) :
    encLN (t :: ts) = Glyph.cons :: ((Val.int (t : ℤ)).enc ++ encLN ts) := rfl

/-! ## The walk program -/

/-- The `mulS` branch of the walk body. -/
def zMULp (mulProg : Cmd) : Cmd := Work.Layout.seqs [.push 0 rZB, .push 0 rZA, mulProg]

/-- The three glyph tests of one element and the branch they select. -/
def zITE (mulProg : Cmd) : Cmd :=
  .ite rZA Glyph.pos
    (.ite rZB (Glyph.bit true)
      (.ite rZC Glyph.iend (.pop 0 rZX) (zMULp mulProg)) (zMULp mulProg))
    (zMULp mulProg)

/-- The `cons` branch of one walk iteration: consume the `cons`, move the element onto the
accumulator, run the test tree, and continue the loop. -/
def zCons (mulProg : Cmd) : Cmd :=
  .seq (Work.Layout.seqs [.pop 1 rZX, Work.Layout.mvVal 1 0 2 3, .pop 0 rZA, .pop 0 rZB,
      .peek 0 rZC])
    (.seq (zITE mulProg) (.set rZL zCont))

/-- One iteration of the walk over the consumed copy of the list. -/
def zBody (mulProg : Cmd) : Cmd :=
  .seq (.peek 1 rZH)
    (.ite rZH Glyph.nil
      (Work.Layout.seqs [.pop 1 rZX, .set rZL zStop])
      (zCons mulProg))

/-- The whole word: `dup`, save the consumed copy on stack `1` below a marker, push the
accumulator `int 1`, walk, remove the marker. -/
def zProg (dupProg pvProg mulProg : Cmd) : Cmd :=
  Work.Layout.seqs [dupProg,
    .set rZX zM, .push 1 rZX,
    Work.Layout.mvVal 0 1 2 3,
    pvProg,
    .set rZL zCont,
    .loop rZL zCont (zBody mulProg),
    .pop 1 rZX]

/-! ## Cost bookkeeping

`gt2 l` is the list of elements of `l` that are `≥ 2`; `zB l` is the paper's
`B = Σ_{t ∈ gt2 l} (t.size - 1)`, `zBsz` the sum of the `Nat.size` of those elements,
`zSisz` the sum of their `isz`, `zSAll` the sum of `isz` over all elements. -/

/-- the elements `≥ 2` of a list of naturals -/
def gt2 (l : List ℕ) : List ℕ := l.filter (fun t => 2 ≤ t)

/-- `B = Σ_{t ≥ 2} (t.size - 1)` -/
def zB (l : List ℕ) : ℕ := ((gt2 l).map (fun t => t.size - 1)).sum

/-- `Σ_{t ≥ 2} t.size` -/
def zBsz (l : List ℕ) : ℕ := ((gt2 l).map Nat.size).sum

/-- `Σ_{t ≥ 2} isz t`, written as `Σ (t.size + 2)` (`isz (t : ℤ) = t.size + 2`) -/
def zSisz (l : List ℕ) : ℕ := ((gt2 l).map (fun t => t.size + 2)).sum

/-- `Σ_{t} isz t`, written as `Σ (t.size + 2)` -/
def zSAll (l : List ℕ) : ℕ := (l.map (fun t => t.size + 2)).sum

/-- number of elements `≥ 2` -/
def zLen2 (l : List ℕ) : ℕ := (gt2 l).length

/-- Cost of walking a whole list: one final `nil` iteration (cost `5`), plus per element `31` +
`16 * (t.size + 2)` for the fixed overhead (`mvVal` is charged separately in `16 * (...)`? no: the
`31` is the fixed part of the body plus the loop test, the `16 * (t.size + 2)` the `mvVal`) plus the
multiplication `Km * (t.size + 2) * (Bz + 2)` for the elements `≥ 2` (the `1`'s are skipped). -/
def zWalkRunCost (Km Bz : ℕ) (ts : List ℕ) : ℕ :=
  5 + (ts.map (fun t => 31 + 16 * (t.size + 2) +
      (if 2 ≤ t then Km * (t.size + 2) * (Bz + 2) else 0))).sum

theorem intList_cons (t : ℕ) (ts : List ℕ) :
    intList (t :: ts) = Val.cons (.int (t : ℤ)) (intList ts) := rfl

/-- the encoding of the list value `intList ts` is `encLN ts` -/
theorem encLN_eq (ts : List ℕ) : encLN ts = (intList ts).enc := by
  induction ts with
  | nil => rfl
  | cons t ts ih => rw [encLN_cons, ih, intList_cons]; rfl

/-- `isz` of a natural number -/
theorem isz_natCast (t : ℕ) : isz (t : ℤ) = t.size + 2 := by
  simp [HvdH.isz, Int.natAbs_natCast]

/-- the encoding size of `intList ts` -/
theorem vsz_intList (ts : List ℕ) :
    vsz (intList ts) = zSAll ts + ts.length + 1 := by
  induction ts with
  | nil => simp [intList, ofList, HvdH.vsz, Val.enc, zSAll]
  | cons t ts ih =>
    rw [intList_cons, Work.ConvR.vsz_cons, ih, Work.ConvR.vsz_int, isz_natCast]
    simp [zSAll, List.sum_cons]
    ring

/-- `gt2` of a `cons` -/
theorem gt2_cons (t : ℕ) (l : List ℕ) :
    gt2 (t :: l) = if 2 ≤ t then t :: gt2 l else gt2 l := by
  unfold gt2
  by_cases h : 2 ≤ t
  · simp [h, List.filter_cons_of_pos]
  · simp [h, List.filter_cons_of_neg]

theorem zBsz_cons (t : ℕ) (l : List ℕ) :
    zBsz (t :: l) = (if 2 ≤ t then t.size else 0) + zBsz l := by
  unfold zBsz
  rw [gt2_cons]
  by_cases h : 2 ≤ t <;> simp [h]

theorem zSisz_cons (t : ℕ) (l : List ℕ) :
    zSisz (t :: l) = (if 2 ≤ t then t.size + 2 else 0) + zSisz l := by
  unfold zSisz
  rw [gt2_cons]
  by_cases h : 2 ≤ t <;> simp [h]

theorem zSAll_cons (t : ℕ) (l : List ℕ) : zSAll (t :: l) = (t.size + 2) + zSAll l := by
  simp [zSAll, List.sum_cons]

theorem zB_cons (t : ℕ) (l : List ℕ) :
    zB (t :: l) = (if 2 ≤ t then t.size - 1 else 0) + zB l := by
  unfold zB
  rw [gt2_cons]
  by_cases h : 2 ≤ t <;> simp [h]

theorem zBsz_nil : zBsz ([] : List ℕ) = 0 := rfl
theorem zSisz_nil : zSisz ([] : List ℕ) = 0 := rfl
theorem zSAll_nil : zSAll ([] : List ℕ) = 0 := rfl


end Work.Transform
