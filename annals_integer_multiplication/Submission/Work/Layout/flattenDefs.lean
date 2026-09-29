import Mathlib
import Submission.Work.Layout.Base
import Submission.Work.Layout.Move

/-!
# Layout area: definitions for the `flattenWord` list word

`flatten` takes a list of lists of values `ofList (xss.map ofList)` on stack 0 and returns the
concatenation `ofList xss.flatten`, touching each glyph of the input `O(1)` times.

The word `Work.Layout.flattenProg` works in three phases, using stacks

* `0` : the input (outer list of lists) and, at the end, the output;
* `1` : the element stack, whose bottom carries the sentinel `gMark`;
* `2` : a scratch stack holding the current inner list (phase 1) resp. the result accumulator
  (phase 3);
* `3`, `4` : the scratch stacks of `Work.Layout.mvVal`.

* **phase 1** (`flatOuterBody` loop): while the top glyph of stack 0 is `Glyph.cons`, pop it and move
  the inner list value to stack 2 (`mvVal 0 2 3 4`), then run the inner loop `flatInnerBody`: while
  the top glyph of stack 2 is `Glyph.cons`, pop it and move the element to the top of stack 1
  (`mvVal 2 1 3 4`).  At the terminator `Glyph.nil` the inner loop stops and pops it.
  Invariant: stack 1 = `encs zs ++ gMark :: _` where `zs` is the reverse of the flattening of the
  lists processed so far.
* **phase 2**: drop the final `nil` of the outer list; push the accumulator `nil` on stack 2.
* **phase 3** (`flatFoldBody` loop): while the top glyph of stack 1 is not `gMark`, move the value on
  top of stack 1 onto stack 2 (`mvVal 1 2 3 4`) and push a `cons` glyph in front of it (so stack 2
  grows the value `ofList` of the elements read so far).  At the sentinel the loop stops and the
  sentinel is popped.
* **final**: move the accumulator from stack 2 to stack 0 (`mvVal 2 0 3 4`).

Since stack 1 receives the elements of the inner lists in reading order, its top value at the end is
the last element of `xss.flatten`; the fold loop then rebuilds `ofList xss.flatten` bottom-up.

This file is pure definitions and elementary lemmas (`sorry`-free).
-/

set_option autoImplicit false

namespace Work.Layout

open HvdH

/-! ## Registers and costs -/

/-- flag register of the outer (unpacking) loop; distinct from the registers `0`--`4` used by `mvVal` -/
def rFlatOut : Reg := 5
/-- flag register of the inner (per-list) loop -/
def rFlatIn : Reg := 6
/-- flag register of the final cons-folding loop -/
def rFlatFold : Reg := 7

/-- Cost bound for the inner loop: one `mvVal`-move per element of `l` plus a final test. -/
def scanCost (l : List Val) : ℕ := (l.map (fun y => 16 * (vsz y + 1) + 5)).sum + 4

/-- Cost bound for the fold loop: one `mvVal`-move and one glyph push per element plus a final test. -/
def foldCost (l : List Val) : ℕ := (l.map (fun y => 16 * (vsz y + 1) + 6)).sum + 4

/-- Cost of one outer-loop iteration that processes the inner list `l` (body only, final test not
included). -/
def outerIterCost (l : List Val) : ℕ := 16 * (vsz (ofList l) + 1) + scanCost l + 8

/-- Cost bound for the outer loop: one iteration per inner list plus a final test. -/
def outerCost (xss : List (List Val)) : ℕ := (xss.map (fun l => outerIterCost l + 1)).sum + 4

/-! ## The program -/

/-- Inner loop body: if the top glyph of stack 2 is `cons`, pop it and move the element to stack 1;
at `nil` stop. -/
def flatInnerBody : Cmd :=
  .seq (.peek 2 rA)
    (.ite rA Glyph.nil
      (.set rFlatIn Glyph.eos)
      (.seq (.pop 2 rB)
        (.seq (mvVal 2 1 3 4)
          (.set rFlatIn Glyph.cons))))

/-- Outer loop body: if the top glyph of stack 0 is `cons`, pop it, move the inner list value to
stack 2, run the inner loop, pop its terminator and continue; at `nil` stop. -/
def flatOuterBody : Cmd :=
  .seq (.peek 0 rA)
    (.ite rA Glyph.nil
      (.set rFlatOut Glyph.eos)
      (.seq (.pop 0 rB)
        (.seq (mvVal 0 2 3 4)
          (.seq (.set rFlatIn Glyph.cons)
            (.seq (.loop rFlatIn Glyph.cons flatInnerBody)
              (.seq (.pop 2 rA)
                (.set rFlatOut Glyph.cons)))))))

/-- Fold loop body: if the top glyph of stack 1 is the sentinel `gMark`, stop; otherwise move the top
value of stack 1 onto stack 2 and push a `cons` glyph in front of it. -/
def flatFoldBody : Cmd :=
  .seq (.peek 1 rA)
    (.ite rA gMark
      (.set rFlatFold Glyph.eos)
      (.seq (mvVal 1 2 3 4)
        (.seq (pushConst 2 Glyph.cons)
          (.set rFlatFold gMark))))

/-- **The flatten word.** -/
def flattenProg : Cmd :=
  .seq (pushConst 1 gMark)
    (.seq (.set rFlatOut Glyph.cons)
      (.seq (.loop rFlatOut Glyph.cons flatOuterBody)
        (.seq (.pop 0 rA)
          (.seq (pushConst 2 Glyph.nil)
            (.seq (.set rFlatFold gMark)
              (.seq (.loop rFlatFold gMark flatFoldBody)
                (.seq (.pop 1 rA)
                  (mvVal 2 0 3 4))))))))

/-! ## Elementaries about the encodings -/

theorem encs_cons' (v : Val) (vs : List Val) : encs (v :: vs) = v.enc ++ encs vs := rfl

theorem encs_append_fl (l₁ l₂ : List Val) : encs (l₁ ++ l₂) = encs l₁ ++ encs l₂ := by
  simp [encs]

theorem ofList_nil' : ofList ([] : List Val) = .nil := rfl

theorem ofList_cons' (y : Val) (ys : List Val) : ofList (y :: ys) = .cons y (ofList ys) := rfl

theorem ofList_enc_nil : (ofList ([] : List Val)).enc = [Glyph.nil] := rfl

theorem ofList_enc_cons (y : Val) (ys : List Val) :
    (ofList (y :: ys)).enc = Glyph.cons :: (y.enc ++ (ofList ys).enc) := rfl

theorem ofList_enc_ne_nil (ys : List Val) : (ofList ys).enc ≠ [] := by
  cases ys with
  | nil => simp [ofList, Val.enc]
  | cons y ys => simp [ofList, Val.enc]

theorem headD_ofList_cons (y : Val) (ys : List Val) (A : List Glyph) :
    ((ofList (y :: ys)).enc ++ A).headD Glyph.eos = Glyph.cons := by
  rw [ofList_enc_cons]; rfl

theorem headD_ofList_nil (A : List Glyph) :
    ((ofList ([] : List Val)).enc ++ A).headD Glyph.eos = Glyph.nil := by
  rw [ofList_enc_nil]; rfl

theorem eq_nil_of_enc_cons_eq_nil {y : Val} {ys : List Val} {A : List Glyph}
    (h : (ofList (y :: ys)).enc ++ A = (ofList ([] : List Val)).enc ++ A) : False := by
  have h2 : Glyph.cons = Glyph.nil := by
    have := congrArg (fun l : List Glyph => l.headD Glyph.eos) h
    rwa [headD_ofList_cons, headD_ofList_nil] at this
  exact gcons_ne_nil h2

/-- The sentinel `gMark` does not occur in the encoding of a list of values. -/
theorem gMark_not_mem_encs (ys : List Val) : gMark ∉ encs ys := by
  intro h
  obtain ⟨l', hl'mem, hl'⟩ := List.mem_flatten.mp h
  obtain ⟨v, -, hv⟩ := List.mem_map.mp hl'mem
  exact gMark_not_mem_enc v (hv ▸ hl')

/-- The head of `v.enc ++ L` (any tail) is never the sentinel `gMark`. -/
theorem headD_enc_append_ne_gMark (v : Val) (L : List Glyph) :
    (v.enc ++ L).headD Glyph.eos ≠ gMark := by
  cases v with
  | int z =>
      by_cases hz : z < 0
      · rw [Val.enc, if_pos hz]
        exact fun h => gMark_ne_neg h.symm
      · rw [Val.enc, if_neg hz]
        exact fun h => gMark_ne_pos h.symm
  | nil => rw [Val.enc]; exact fun h => gMark_ne_nil h.symm
  | cons a b => rw [Val.enc]; exact fun h => gMark_ne_cons h.symm

/-- `encs (v :: vs) ++ L` starts with the encoding of `v`. -/
theorem headD_encs_cons_ne_gMark (v : Val) (vs : List Val) (L : List Glyph) :
    (encs (v :: vs) ++ L).headD Glyph.eos ≠ gMark := by
  rw [encs_cons', List.append_assoc]
  exact headD_enc_append_ne_gMark v _

/-- Splitting off the leading `cons` of a nonempty `ofList`. -/
theorem ofList_enc_cons_append (y : Val) (ys : List Val) (A : List Glyph) :
    (ofList (y :: ys)).enc ++ A = Glyph.cons :: (y.enc ++ ((ofList ys).enc ++ A)) := by
  rw [ofList_enc_cons, List.cons_append, List.append_assoc]

/-! ## The stacks the program touches -/

theorem cmdTouches_mvVal_fl (a b c d : Stk) : cmdTouches (mvVal a b c d) = {a, b, c, d} := by
  rw [mvVal, cmdTouches, cmdTouches_mvA, cmdTouches_mvB]
  ext k
  simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union]
  tauto

theorem cmdTouches_flattenProg : cmdTouches flattenProg = {0, 1, 2, 3, 4} := by
  simp only [flattenProg, flatOuterBody, flatInnerBody, flatFoldBody, pushConst, seqs,
    cmdTouches, cmdTouches_mvVal_fl]
  decide

/-- Membership test for the set of stacks the flatten word touches. -/
theorem notMem_01234 {k : Stk} (h0 : k ≠ 0) (h1 : k ≠ 1) (h2 : k ≠ 2) (h3 : k ≠ 3)
    (h4 : k ≠ 4) : k ∉ ({0, 1, 2, 3, 4} : Finset Stk) := by
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

end Work.Layout
