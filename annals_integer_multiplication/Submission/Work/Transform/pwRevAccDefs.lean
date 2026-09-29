import Mathlib
import Submission.Work.Transform.pwBase

/-!
# `Work.Transform.pwRevAcc`: definitions

Definitions and elementary encoding facts for the reversal-accumulation word `pwRevAcc`
(traverse the `cons`-list `ofList xs` above the frame marker `Pw.gM` on `src`, rebuild
`ofList xs.reverse` above a freshly pushed `Pw.gM` on `dst`).

The program is `pwRaProg`; its main loop is `pwRaBody`, whose "one element" block is `pwRaElem`.
The destination stack receives `pwRaBlocks xs` (the per-element blocks, in reverse order) followed
by the pushed `nil` and the pushed `gM`.

This module is self-contained: it imports only `pwBase` (which provides the raw toolkit over the
marker `Pw.gM`) and copies the few `ofList` encoding facts it needs, so that it does not depend on
files that are being edited concurrently.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.Transform

open HvdH

/-! ## Elementary `ofList` encoding facts (local copies) -/

theorem ra_cons_enc (a b : Val) : (Val.cons a b).enc = Glyph.cons :: (a.enc ++ b.enc) := rfl

theorem ra_ofList_cons (a : Val) (as : List Val) : ofList (a :: as) = Val.cons a (ofList as) := rfl

theorem ra_ofList_nil : ofList ([] : List Val) = Val.nil := rfl

/-- The `ofList` encoding is a chain of `cons`-blocks followed by a single `nil`. -/
theorem ra_enc_ofList_flat (xs : List Val) :
    (ofList xs).enc = (xs.map (fun v => Glyph.cons :: v.enc)).flatten ++ [Glyph.nil] := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    show (Val.cons a (ofList as)).enc = _
    rw [show (Val.cons a (ofList as)).enc = Glyph.cons :: (a.enc ++ (ofList as).enc) from rfl, ih]
    simp [List.map_cons, List.flatten_cons, List.cons_append, List.append_assoc]

/-! ## Registers -/

/-- Scratch register for single-glyph moves. -/
def pwrA : Reg := 1

/-- Scratch register of the reversible loops (`Pw.tLoop`, `Pw.dropMarked`). -/
def pwrB : Reg := 2

/-- Loop-control register of the reversal loop. -/
def pwrC : Reg := 0

theorem pwrA_ne_pwrB : pwrA ≠ pwrB := by decide

theorem pwrA_ne_pwrC : pwrA ≠ pwrC := by decide

theorem pwrB_ne_pwrC : pwrB ≠ pwrC := by decide

/-! ## The blocks pushed on the destination stack -/

/-- The glyph block of one element: the leading `cons` followed by the encoding of the value. -/
abbrev pwRaBlock (v : Val) : List Glyph := Glyph.cons :: v.enc

/-- Content pushed on the destination stack after the elements `vs` (in order) have been
processed: their blocks in reverse order. -/
abbrev pwRaBlocks (vs : List Val) : List Glyph := (vs.reverse.map pwRaBlock).flatten

theorem pwRaBlock_eq (v : Val) : pwRaBlock v = Glyph.cons :: v.enc := rfl

theorem pwRaBlocks_nil : pwRaBlocks ([] : List Val) = [] := rfl

theorem pwRaBlock_enc (v : Val) : pwRaBlock v = (fun w : Val => Glyph.cons :: w.enc) v := rfl

theorem pwRaBlocks_as_flatten (vs : List Val) :
    pwRaBlocks vs = (vs.reverse.map (fun v => Glyph.cons :: v.enc)).flatten := rfl

theorem pwRaBlocks_concat (pre : List Val) (v : Val) :
    pwRaBlocks (pre ++ [v]) = pwRaBlock v ++ pwRaBlocks pre := by
  rw [pwRaBlocks, pwRaBlocks, List.reverse_append, List.map_append]
  rfl

/-- `pwRaBlocks vs` is the body of `(ofList vs.reverse).enc` (everything but the trailing `nil`). -/
theorem pwRaBlocks_append_nil (vs : List Val) :
    pwRaBlocks vs ++ [Glyph.nil] = (ofList vs.reverse).enc := by
  rw [pwRaBlocks_as_flatten, ra_enc_ofList_flat]

theorem pwRaBlocks_length (vs : List Val) :
    (pwRaBlocks vs).length + 1 = (ofList vs.reverse).enc.length := by
  rw [← pwRaBlocks_append_nil vs, List.length_append, List.length_singleton]

/-! ## Splitting one cell off an `ofList` encoding -/

theorem enc_ofList_cons_eq (v : Val) (vs : List Val) :
    (ofList (v :: vs)).enc = pwRaBlock v ++ (ofList vs).enc := rfl

theorem enc_ofList_cons_length (v : Val) (vs : List Val) :
    (ofList (v :: vs)).enc.length = v.enc.length + 1 + (ofList vs).enc.length := by
  rw [enc_ofList_cons_eq, List.length_append]
  rfl

theorem enc_ofList_nil_eq : (ofList ([] : List Val)).enc = [Glyph.nil] := rfl

theorem enc_int_length (z : ℤ) : (Val.int z).enc.length = z.natAbs.size + 2 := by
  rw [Work.IntLib.vsz_int, Work.IntLib.isz_eq]

theorem enc_int_eq (z : ℤ) :
    (Val.int z).enc = (if z < 0 then Glyph.neg else Glyph.pos) ::
      ((Computability.encodeNat z.natAbs).map Glyph.bit ++ [Glyph.iend]) := rfl

/-! ## The program -/

/-- The "one element" block of the reversal loop: `Pw.storeMag` pops the sign glyph of the integer
on top of `src` onto `ds` and moves its bits (most significant first) above a fresh `gM` on `sp`;
then `dst` receives `iend`, the bits (moved from `sp`, restoring `sp` with `Pw.dropMarked`), the
sign (from `ds`) and finally the leading `cons`. -/
def pwRaElem (src dst sp ds : Stk) : Cmd :=
  .seq (Pw.storeMag src sp ds pwrA pwrB)
   (.seq (.set pwrA Glyph.iend)
    (.seq (.push dst pwrA)
     (.seq (Pw.tLoop sp Pw.gM dst pwrB)
      (.seq (Pw.dropMarked sp pwrA pwrB)
       (.seq (.pop ds pwrA)
        (.seq (.push dst pwrA)
         (.seq (.set pwrA Glyph.cons)
          (.push dst pwrA))))))))

/-- One iteration of the reversal loop: pop the leading glyph of `src`; if it is a `cons` (an
element follows) run `pwRaElem` and continue, otherwise (the list ends with `nil`) stop. -/
def pwRaBody (src dst sp ds : Stk) : Cmd :=
  .seq (.pop src pwrC)
   (.ite pwrC Glyph.cons
     (.seq (pwRaElem src dst sp ds) (.set pwrC Glyph.eos))
     (.set pwrC Glyph.iend))

/-- The whole reversal-accumulation program: push a fresh `gM` and a `nil` on `dst`, then run the
reversal loop. -/
def pwRaProg (src dst sp ds : Stk) : Cmd :=
  .seq (.set pwrA Pw.gM)
   (.seq (.push dst pwrA)
    (.seq (.set pwrA Glyph.nil)
     (.seq (.push dst pwrA)
      (.seq (.set pwrC Glyph.eos)
       (.loop pwrC Glyph.eos (pwRaBody src dst sp ds))))))

end Work.Transform
