import Mathlib
import Submission.Work.SynFFT.axisKit
import Submission.Work.Kernel.kernelLib
import Submission.Work.Layout.AA.ProgAux
import Submission.Work.Layout.AA.unconsTo_ev
import Submission.Work.Layout.AA.prependTo_ev

/-!
# `Work.SynFFT.mrgLvDefs`: the one-merge-level word (definitions + size facts)

[Same doc comment as the target lemma.] The program built here performs one merge level of the
transpose word: with `stateVal Gs` (the value `ofList (Gs.map grpVal)`) on top of stack 0, it
reproduces `stateVal (mLevel Gs)`, in time linear in `vsz (stateVal Gs)`.

The implementation is

`pushMarker ; mvVal 0 inp ; pushMarker ; pushMarker 0 ; (merge walk on stack 0) ;
 pushMarker ; pushNil ; (fold on stack 0) ; clearTo 0 ; mvVal out 0 ; clearTo out ; clearTo inp ; clearTo tmp`

* the input `cons`-chain is on stack `lvIn = 9` above a boundary marker;
* the accumulator is a *raw* stack of values (each a `grpVal`) above a boundary marker on stack 0;
* `lvTmp = 10` carries the pending element of a pair;
* at the end the accumulator (whose top-down order is `(mLevel Gs).reverse`) is folded into a list
  value on `lvOut = 11` with `prependTo`, which produces `ofList (mLevel Gs)` without a reversal.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.SynFFT

open HvdH

/-! ## The raw `cons`-chain encoding of a list of values -/

/-- `encsC vs` is the glyph list occupied on a raw stack by the `cons`-chain of the values `vs`:
one `cons` glyph followed by the encoding of each element (no trailing `nil`). -/
def encsC (vs : List Val) : List Glyph := (vs.map (fun v => Glyph.cons :: v.enc)).flatten

@[simp] theorem encsC_nil : encsC ([] : List Val) = [] := rfl

theorem encsC_cons (v : Val) (vs : List Val) :
    encsC (v :: vs) = (Glyph.cons :: v.enc) ++ encsC vs := rfl

theorem encsC_append (vs ws : List Val) : encsC (vs ++ ws) = encsC vs ++ encsC ws := by
  simp [encsC, List.map_append]

/-- the `cons`-chain encoding of `ofList vs` ends in the `nil` of `ofList`. -/
theorem enc_ofList (vs : List Val) : (ofList vs).enc = encsC vs ++ [Glyph.nil] := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
      have h : ofList (v :: vs) = Val.cons v (ofList vs) := rfl
      rw [h, Val.enc, ih, encsC_cons]
      simp [List.append_assoc]

/-- size of the `cons`-chain encoding of a list of values. -/
theorem length_encsC (vs : List Val) : (encsC vs).length = (vs.map vsz).sum + vs.length := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
      rw [encsC_cons, List.length_append, ih]
      simp only [List.length_cons, List.map_cons, List.sum_cons, vsz]
      omega

/-- size of a list value. -/
theorem vsz_ofList (vs : List Val) : vsz (ofList vs) = (vs.map vsz).sum + vs.length + 1 := by
  rw [vsz, enc_ofList, List.length_append, length_encsC]
  simp

/-- `Σᵢ (f xᵢ + 1) = (Σᵢ f xᵢ) + length`. -/
theorem sum_map_add_one {α : Type} (l : List α) (f : α → ℕ) :
    (l.map (fun x => f x + 1)).sum = (l.map f).sum + l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; omega

/-! ## Size bookkeeping for the merge walk -/

/-- `gSz Ls` is the total size of a list of groups as a raw stack of values, up to one unit:
`Σ_g (vsz (grpVal g) + 1)`. -/
def gSz (Ls : List (List (List Val))) : ℕ := (Ls.map (fun g => vsz (grpVal g) + 1)).sum

/-- `vSz vs` is `Σ_v (vsz v + 1)`: the size of a raw stack of values, up to one unit. -/
def vSz (vs : List Val) : ℕ := (vs.map (fun v => vsz v + 1)).sum

theorem gSz_append (xs ys : List (List (List Val))) : gSz (xs ++ ys) = gSz xs + gSz ys := by
  simp [gSz, List.map_append, List.sum_append]

theorem vSz_append (xs ys : List Val) : vSz (xs ++ ys) = vSz xs + vSz ys := by
  simp [vSz, List.map_append, List.sum_append]

theorem vSz_eq (vs : List Val) : vsz (ofList vs) = vSz vs + 1 := by
  rw [vsz_ofList, vSz, sum_map_add_one]

theorem vSz_map_grpVal (Ls : List (List (List Val))) : vSz (Ls.map grpVal) = gSz Ls := by
  rw [vSz, gSz, List.map_map]
  rfl

theorem vsz_stateVal (Ls : List (List (List Val))) : vsz (stateVal Ls) = gSz Ls + 1 := by
  rw [stateVal, vsz_ofList, gSz, sum_map_add_one, List.length_map]
  have h : ((Ls.map grpVal).map vsz).sum = (Ls.map fun g => vsz (grpVal g)).sum := by
    rw [List.map_map]; rfl
  rw [h]

/-! ## Stacks and registers -/

/-- stack carrying the not-yet-processed input `cons`-chain -/
def lvIn : Stk := 9
/-- scratch stack holding the pending element of a pair -/
def lvTmp : Stk := 10
/-- stack carrying the output list value built by the fold -/
def lvOut : Stk := 11
/-- first scratch stack for the value movers -/
def lvS1 : Stk := 12
/-- second scratch stack for the value movers -/
def lvS2 : Stk := 13
/-- loop flag register (`cons` = continue, `eos` = stop) -/
def lvF : Reg := 5
/-- register receiving a peeked glyph -/
def lvP : Reg := 6
/-- register used to push marker glyphs -/
def lvG : Reg := 7

/-! ## The program -/

/-- the "input exhausted after one element" branch of a merge step: push the pending element onto
the accumulator and stop. -/
def mergeBodyLast : Cmd :=
  Work.Layout.seqs [ Work.Layout.mvVal lvTmp 0 lvS1 lvS2, HvdH.Cmd.set lvF Glyph.eos ]

/-- the "there is a second element" branch of a merge step: pop it onto the accumulator, move the
pending element on top of it, merge the two with `hp`, and continue. -/
def mergeBodyPair (hp : Cmd) : Cmd :=
  Work.Layout.seqs [ Work.Layout.unconsTo lvIn 0 lvS1 lvS2 lvP,
                     Work.Layout.mvVal lvTmp 0 lvS1 lvS2,
                     hp,
                     HvdH.Cmd.set lvF Glyph.cons ]

/-- the tail of a merge step, once the first element has been popped into `lvTmp`: if the input is
exhausted push that element onto the accumulator and stop, otherwise pop a second element and merge
the two. -/
def mergeTail (hp : Cmd) : Cmd :=
  Work.Layout.seqs
    [ HvdH.Cmd.peek lvIn lvP,
      HvdH.Cmd.ite lvP Glyph.nil mergeBodyLast (mergeBodyPair hp) ]

/-- the middle of a merge step: pop the leading element of the input into `lvTmp`, then `mergeTail`. -/
def mergeMid (hp : Cmd) : Cmd :=
  Work.Layout.seqs [ Work.Layout.unconsTo lvIn lvTmp lvS1 lvS2 lvP, mergeTail hp ]

/-- one iteration of the merge walk: if the input `cons`-chain on `lvIn` is exhausted stop, else pop
its leading element and run `mergeMid`. -/
def mergeStep (hp : Cmd) : Cmd :=
  Work.Layout.seqs
    [ HvdH.Cmd.peek lvIn lvP,
      HvdH.Cmd.ite lvP Glyph.nil (HvdH.Cmd.set lvF Glyph.eos) (mergeMid hp) ]

/-- the merge walk (one merge level), starting from a clean flag. -/
def mergeLoop (hp : Cmd) : Cmd :=
  Work.Layout.seqs [HvdH.Cmd.set lvF Glyph.cons, HvdH.Cmd.loop lvF Glyph.cons (mergeStep hp)]

/-- the "accumulator nonempty" branch of a fold step: pop the top value of stack 0 and prepend it to
the list value on `lvOut`. -/
def foldBody : Cmd :=
  Work.Layout.seqs [ Work.Layout.prependTo 0 lvOut lvS1 lvS2 lvP, HvdH.Cmd.set lvF Glyph.cons ]

/-- one iteration of the fold: stop when the accumulator on stack 0 is exhausted (its top glyph is
the boundary marker `gMark`), else prepend the top value to the list value on `lvOut`. -/
def foldStep_xmrgLvDefs : Cmd :=
  Work.Layout.seqs
    [ HvdH.Cmd.peek 0 lvP,
      HvdH.Cmd.ite lvP Work.Layout.gMark (HvdH.Cmd.set lvF Glyph.eos) foldBody ]

/-- the fold of the accumulator into a list value, starting from a clean flag. -/
def foldLoop : Cmd :=
  Work.Layout.seqs [HvdH.Cmd.set lvF Glyph.cons, HvdH.Cmd.loop lvF Glyph.cons foldStep_xmrgLvDefs]

/-- prologue of the merge-level word: put a boundary marker on `lvIn`, move `stateVal Gs` there,
mark `lvTmp` and put the accumulator's boundary marker on stack 0. -/
def mergeSetup : Cmd :=
  Work.Layout.seqs
    [ Work.Kernel.pushGlyphs [Work.Layout.gMark] lvIn lvG,
      Work.Layout.mvVal 0 lvIn lvS1 lvS2,
      Work.Kernel.pushGlyphs [Work.Layout.gMark] lvTmp lvG,
      Work.Kernel.pushGlyphs [Work.Layout.gMark] 0 lvG ]

/-- initialisation of the output list value on `lvOut`. -/
def outSetup : Cmd :=
  Work.Layout.seqs
    [ Work.Kernel.pushGlyphs [Work.Layout.gMark] lvOut lvG,
      Work.Kernel.pushGlyphs [Glyph.nil] lvOut lvG ]

/-- epilogue of the merge-level word: drop the accumulator's marker, move the output list value onto
stack 0, and restore the three working stacks. -/
def mergeFinish : Cmd :=
  Work.Layout.seqs
    [ Work.Layout.clearTo 0 lvP lvF,
      Work.Layout.mvVal lvOut 0 lvS1 lvS2,
      Work.Layout.clearTo lvOut lvP lvF,
      Work.Layout.clearTo lvIn lvP lvF,
      Work.Layout.clearTo lvTmp lvP lvF ]

/-- **the one-merge-level word**: `stateVal Gs ↦ stateVal (mLevel Gs)` on stack 0. -/
def mergeLevelProg (hp : Cmd) : Cmd :=
  Work.Layout.seqs [mergeSetup, mergeLoop hp, outSetup, foldLoop, mergeFinish]

end Work.SynFFT
