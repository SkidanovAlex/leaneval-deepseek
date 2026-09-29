import Mathlib
import Submission.Work.IntLib.evDefs
import Submission.Work.IntLib.range_blk_enc
import Submission.Work.IntLib.Shift.Base
import Submission.Work.Layout.Base

/-!
# `IntLib` / `evChainMove`: the chain-reading word

`evChainMove` iterates a single-value reader `readG` (which reads `int h` off stack 0 and *prepends*
its reversed encoding to stack `k`) over a whole `cons`-chain `intList hs`.

Writing `e d := Val.enc (.int d)`, the encoding of the chain is

`Val.enc (intList l) = flatMap (fun d => Glyph.cons :: e d) l ++ [Glyph.nil]`

(`enc_intList_flatMap`), so its reversal is `[Glyph.nil] ++ revAcc l` with

`revAcc l := (flatMap (fun d => Glyph.cons :: e d) l).reverse`.

The loop of the word processes the chain front to back, and for each entry `d` first pushes a
`cons` glyph and then runs `readG`: after the entry the stack `k` content has grown by
`(e d).reverse ++ [cons]`, i.e. by one more block of `revAcc`.  When the chain is exhausted
(a `nil` is on top of stack 0) the loop stops; the final `nil` is then popped and pushed on
stack `k`, which reproduces `(Val.enc (intList hs)).reverse` exactly.
-/

set_option autoImplicit false

namespace Work.IntLib

open HvdH
open Work.Layout

/-- The block that one processed entry `d` adds on stack `k`: the reversed encoding of `int d`
followed by the `cons` marker of the chain cell. -/
def revBlk (d : ℕ) : List Glyph := (Val.enc (.int (d : ℤ))).reverse ++ [Glyph.cons]

/-- `revAcc l` is the content accumulated on stack `k` by the loop of `evChainMove` after
processing the whole chain `l`: the blocks of the entries, in reverse order. -/
def revAcc (l : List ℕ) : List Glyph :=
  (List.flatMap (fun d : ℕ => Glyph.cons :: (Val.int (d : ℤ)).enc) l).reverse

@[simp] theorem revAcc_nil : revAcc [] = [] := rfl

theorem revAcc_cons (h : ℕ) (t : List ℕ) : revAcc (h :: t) = revAcc t ++ revBlk h := by
  simp only [revAcc, revBlk, List.flatMap_cons, List.reverse_append, List.reverse_cons]

theorem revAcc_cons_append (h : ℕ) (t : List ℕ) (A : List Glyph) :
    revAcc (h :: t) ++ A = revAcc t ++ (Val.enc (.int (h : ℤ))).reverse ++ [Glyph.cons] ++ A := by
  rw [revAcc_cons, revBlk]
  simp only [List.append_assoc]

/-- The reversal of the encoding of a chain. -/
theorem rev_enc_intList (l : List ℕ) :
    (Val.enc (HvdH.intList l)).reverse = Glyph.nil :: revAcc l := by
  rw [enc_intList_flatMap, List.reverse_append, List.reverse_singleton]
  rfl

/-- The chain encoding starts with a `cons` cell. -/
theorem enc_intList_cons (h : ℕ) (t : List ℕ) :
    Val.enc (HvdH.intList (h :: t)) =
      Glyph.cons :: (Val.enc (.int (h : ℤ)) ++ Val.enc (HvdH.intList t)) := rfl

/-- The chain encoding of `[]` is the single glyph `nil`. -/
theorem enc_intList_nil : Val.enc (HvdH.intList ([] : List ℕ)) = [Glyph.nil] := rfl

/-! ## The programs -/

/-- The body of the chain loop: if the top of stack 0 is a `cons` cell, drop it, push it on stack
`k`, run the single-value reader `readG` and set the loop flag according to whether the chain still
has a `cons` cell on top. -/
def evChainBody (k : Stk) (readG : Cmd) : Cmd :=
  seqs [.peek 0 rX,
        .ite rX Glyph.cons
          (seqs [.pop 0 rX, .push k rX, readG, .peek 0 rX,
                 .ite rX Glyph.cons (.set rLp fGo) (.set rLp fStop)])
          (.set rLp fStop)]

/-- The chain loop. -/
def evChainLoopP (k : Stk) (readG : Cmd) : Cmd := .loop rLp fGo (evChainBody k readG)

/-- The chain word: set the flag, run the loop, then move the chain's `nil` onto stack `k`. -/
def evChainProg (k : Stk) (readG : Cmd) : Cmd :=
  seqs [.set rLp fGo, evChainLoopP k readG, .pop 0 rX, .push k rX]

end Work.IntLib
