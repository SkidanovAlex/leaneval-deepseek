import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Kernel.Raw
import Submission.Work.Kernel.Pend
import Submission.Work.Kernel.dropValueDefs
import Submission.Work.Kernel.dropValueChainEval

/-!
# `crtJoinWord`: joining two lists elementwise (`zipRec`) — shared definitions

`Work.MainP.crtJoinWord` asks for a StackLang word turning the value stack
`ofList xs :: ofList ws :: rest` into `ofList (zipRec xs ws) :: rest` at cost linear in
`vsz (ofList xs) + vsz (ofList ws)`, where `zipRec xs ws = List.zipWith (fun x w => .cons w x) xs ws`.

This module fixes the *concrete* glyph-level data structures, programs and states used by that proof.
Everything here is `sorry`-free and describes a loop-based (no recursion, hence valid for every
`main`) program; it is meant to be imported by the lemma files that prove the `Eval` behaviour of the
individual loops.

## The algorithm (four passes over the glyph stream)

Writing `X = (ofList xs).enc = C x₁ C x₂ … C xₙ N` and `W = (ofList ws).enc = C w₁ … C wₙ N`
(where `xᵢ = (xs[i]).enc`, `wᵢ = (ws[i]).enc` and `C`/`N` are the `cons`/`nil` glyphs), the input
stack 0 reads `X ++ W ++ rest` and we must produce
`C (C w₁ x₁) C (C w₂ x₂) … C (C wₙ xₙ) N ++ rest`.

Since the encoded values are self-delimiting, a *pending-subtree counter* (a unary region of `jtok`
glyphs above a `jbase` marker on stack 1, exactly as in `Work.Kernel.dropValue`) determines the end
of the next value on stack 0; a single glyph is moved per round.

* `consumeList dst cnt` (passes 1 and 2): while stack 0's top glyph is `cons`, consume it, push a
  `jdelim` marker on the count region `cnt`, then copy the whole element encoding from stack 0 to
  `dst` (reversing it, since it is pushed) while pushing one `jtok` per copied glyph on `cnt`.
  Applied to `X` this leaves stack 2 holding `xₙ^R … x₁^R` and stack 6 the unary block counts
  `tok^{|xₙ|} delim … tok^{|x₁|} delim`; applied to `W` it fills stack 3 and stack 7.
* `joinPhase` (passes 3 and 4): push `N`, then, for `i = n, n-1, …, 1`: copy the `xᵢ` block from
  stack 2 and the `wᵢ` block from stack 3 (each delimited by its own unary token count on stacks 6
  and 7), then push two `cons` glyphs.  Reversing the pushes gives the output.

Stack usage: 0 = value stack, 1 = the scan counter region (always restored), 2/3 = the two element
buffers, 6/7 = the two unary block-count regions, 4/5 hold the constant glyphs used by `set`/`push`.
-/

set_option autoImplicit false

namespace Work.MainP

open HvdH

/-! ## Glyphs -/

/-- Counter token of the pending-subtree scan (also the token of the block-count regions). -/
abbrev jtok : Glyph := Work.Kernel.dropValue_tok

/-- Base marker of the pending-subtree scan (the canonical scan state of the Kernel area). -/
abbrev jbase : Glyph := Work.Kernel.dropValue_base

/-- Separator between the unary block counts of two consecutive elements. -/
def jdelim : Glyph := .mk 2

/-- Base marker of a unary block-count region. -/
def jcb : Glyph := .mk 3

@[simp] theorem jtok_eq : jtok = Glyph.mk 0 := rfl
@[simp] theorem jbase_eq : jbase = Glyph.mk 1 := rfl
@[simp] theorem jdelim_eq : jdelim = Glyph.mk 2 := rfl
@[simp] theorem jcb_eq : jcb = Glyph.mk 3 := rfl

theorem jdelim_ne_tok : jdelim ≠ jtok := by decide
theorem jdelim_ne_base : jdelim ≠ jbase := by decide
theorem jdelim_ne_cb : jdelim ≠ jcb := by decide
theorem jcb_ne_tok : jcb ≠ jtok := by decide
theorem jcb_ne_base : jcb ≠ jbase := by decide
theorem cons_ne_jtok : Glyph.cons ≠ jtok := by decide
theorem cons_ne_jbase : Glyph.cons ≠ jbase := by decide
theorem cons_ne_jdelim : Glyph.cons ≠ jdelim := by decide
theorem cons_ne_jcb : Glyph.cons ≠ jcb := by decide
theorem nil_ne_jtok : Glyph.nil ≠ jtok := by decide
theorem nil_ne_jbase : Glyph.nil ≠ jbase := by decide
theorem nil_ne_jdelim : Glyph.nil ≠ jdelim := by decide
theorem nil_ne_jcb : Glyph.nil ≠ jcb := by decide

/-! ## The programs -/

/-- One round of the element scan: pop a counter token from stack 1, pop a glyph of the element
being copied from stack 0 into register 2, push it on `dst`, push one token on `cnt`, let
`Work.Kernel.dropValue_chain` update the pending-subtree counter, and refresh the test register. -/
def scanBody (dst cnt : Stk) : Cmd :=
  .seq (.pop 1 2)
    (.seq (.pop 0 2)
      (.seq (.push dst 2)
        (.seq (.push cnt 3)
          (.seq Work.Kernel.dropValue_chain
            (.seq (.set 2 jbase) (.peek 1 1))))))

/-- Copy the next value on stack 0 to `dst` (reversed: the glyphs are pushed), pushing one `jtok`
per glyph on `cnt`.  The pending-subtree counter region on stack 1 (`Work.Kernel.dropValue_pre`
creates it, `Work.Kernel.dropValue_stk1` describes it) stops the scan exactly after the value. -/
def scanVal (dst cnt : Stk) : Cmd :=
  .seq Work.Kernel.dropValue_pre
    (.seq (.loop 1 jtok (scanBody dst cnt)) (.pop 1 0))

/-- One element of the list on stack 0: consume its `cons` glyph, open a fresh unary block on
`cnt`, copy the element encoding to `dst`, refresh the test register. -/
def elemBody (dst cnt : Stk) : Cmd :=
  .seq (.pop 0 1)
    (.seq (.push cnt 5)
      (.seq (scanVal dst cnt) (.peek 0 1)))

/-- While the top glyph of stack 0 is `cons`, consume one element of the list as in `elemBody`.
Stops with the terminating `nil` of the list still on top of stack 0. -/
def consumeList (dst cnt : Stk) : Cmd :=
  .seq (.peek 0 1) (.loop 1 Glyph.cons (elemBody dst cnt))

/-- `consumeList` followed by discarding the `nil`: stack 0 is left with the tail of the input. -/
def consumeListN (dst cnt : Stk) : Cmd := .seq (consumeList dst cnt) (.pop 0 1)

/-- Copy one block: while `cnt`'s top glyph is a `jtok`, consume the token, pop one glyph of the
block from `buf` and push it on stack 0. -/
def blkLoop (cnt buf : Stk) : Cmd :=
  .seq (.peek cnt 1)
    (.loop 1 jtok
      (.seq (.pop cnt 1) (.seq (.pop buf 1) (.seq (.push 0 1) (.peek cnt 1)))))

/-- One element of the interleaving phase: copy the `xᵢ` block (stack 2, counted on stack 6), drop
its `jdelim`, do the same for the `wᵢ` block (stack 3, counted on stack 7), push the two `cons`
glyphs of the pair, refresh the outer test. -/
def joinBody : Cmd :=
  .seq (blkLoop 6 2)
    (.seq (.pop 6 1)
      (.seq (blkLoop 7 3)
        (.seq (.pop 7 1)
          (.seq (.push 0 4)
            (.seq (.push 0 4) (.peek 6 1))))))

/-- The interleaving loop: one round per element pair. -/
def joinLoop : Cmd := .seq (.peek 6 1) (.loop 1 jtok joinBody)

/-- The interleaving phase: push the terminating `nil`, run the loop, discard the two base markers
of the count regions. -/
def joinPhase : Cmd :=
  .seq (.set 4 Glyph.cons)
    (.seq (.set 2 Glyph.nil)
      (.seq (.push 0 2)
        (.seq joinLoop (.seq (.pop 6 1) (.pop 7 1)))))

/-- Set up the constant registers and the two base markers of the count regions. -/
def jsetup : Cmd :=
  .seq (.set 5 jdelim)
    (.seq (.set 3 jcb) (.seq (.push 6 3) (.seq (.push 7 3) (.set 3 jtok))))

/-- The whole word: set up, consume the first list, consume the second list, interleave. -/
def joinProg : Cmd :=
  .seq jsetup (.seq (consumeListN 2 6) (.seq (consumeListN 3 7) joinPhase))

/-! ## Glyph-level descriptions of the data

For a list `Gs = [g₁, …, gₙ]` of element encodings we write down the exact content of the stacks
involved.  These functions are the interface between the `Eval` lemmas about the programs above and
the `WordR` statement about `ofList`/`zipRec`. -/

/-- Stack 0 while the elements `Gs` remain: `C g₁ C g₂ … C gₙ N`. -/
def listEncR (Gs : List (List Glyph)) : List Glyph :=
  (Gs.map (fun g => Glyph.cons :: g)).flatten ++ [Glyph.nil]

/-- The buffer (`dst` of `consumeList`) after all elements `Gs` have been copied: the pushed glyphs
in reverse, i.e. the element encodings in reverse element order, each reversed. -/
def bufReg (Gs : List (List Glyph)) : List Glyph := Gs.flatten.reverse

/-- The count region (`cnt` of `consumeList`) after all elements `Gs` have been counted: for
`Gs = [g₁, …, gₙ]` the unary blocks `tok^{|gᵢ|}` separated by `jdelim`, in reverse element order. -/
def cntReg (Gs : List (List Glyph)) : List Glyph :=
  (Gs.reverse.map (fun g => List.replicate g.length jtok ++ [jdelim])).flatten

/-- The output glyph string of the interleaving of `Ws` and `Gs`: for each element index `i`,
`C C wᵢ xᵢ`, then the terminating `N`. -/
def outGlyphs (Ws Gs : List (List Glyph)) : List Glyph :=
  ((List.zipWith (fun w g => [Glyph.cons, Glyph.cons] ++ w ++ g) Ws Gs).flatten) ++ [Glyph.nil]

/-! ## States -/

/-- Pre-state of `consumeListN dst cnt`: stack 0 holds the remaining list encoding followed by the
untouched tail `t`, `dst` the already copied buffer `b`, `cnt` the base marker followed by the
already pushed count region `c`, register 5 the `jdelim` glyph. -/
def clPre (s : State) (dst cnt : Stk) (Gs : List (List Glyph)) (t b c : List Glyph) : State :=
  (((s.updStk 0 (listEncR Gs ++ t)).updStk dst b).updStk cnt (jcb :: c)).updReg 5 jdelim

/-- Post-state of `consumeListN dst cnt`. -/
def clPost (s : State) (dst cnt : Stk) (t b c : List Glyph) : State :=
  ((s.updStk 0 t).updStk dst b).updStk cnt c

/-- Pre-state of `joinPhase`: stack 0 holds the untouched tail `t`, stack 2 the reversed `x`-blocks
of `Gs`, stack 3 the reversed `w`-blocks of `Ws`, stack 6 (resp. 7) the unary block counts of `Gs`
(resp. `Ws`) above the base marker `jcb`, everything else as in `s`. -/
def jpPre (s : State) (Ws Gs : List (List Glyph)) (t : List Glyph) : State :=
  ((((s.updStk 0 t).updStk 2 (bufReg Gs ++ s.stk 2)).updStk 3 (bufReg Ws ++ s.stk 3)).updStk 6
      (cntReg Gs ++ jcb :: s.stk 6)).updStk 7 (cntReg Ws ++ jcb :: s.stk 7)

/-- Post-state of `joinPhase`: stack 0 carries the output glyph string followed by the tail `t`;
everything else is back to `s`. -/
def jpPost (s : State) (Ws Gs : List (List Glyph)) (t : List Glyph) : State :=
  s.updStk 0 (outGlyphs Ws Gs ++ t)

/-! ## Elementary facts about the descriptions -/

@[simp] theorem listEncR_nil : listEncR ([] : List (List Glyph)) = [Glyph.nil] := rfl

theorem listEncR_cons (g : List Glyph) (Gs : List (List Glyph)) :
    listEncR (g :: Gs) = Glyph.cons :: (g ++ listEncR Gs) := by
  simp [listEncR, List.map_cons, List.flatten_cons, List.cons_append]

theorem cntReg_nil : cntReg ([] : List (List Glyph)) = [] := rfl

theorem bufReg_nil : bufReg ([] : List (List Glyph)) = [] := rfl

theorem bufReg_cons (g : List Glyph) (Gs : List (List Glyph)) :
    bufReg (g :: Gs) = bufReg Gs ++ g.reverse := by
  simp [bufReg, List.flatten_cons, List.reverse_append]

theorem cntReg_cons (g : List Glyph) (Gs : List (List Glyph)) :
    cntReg (g :: Gs) = cntReg Gs ++ (List.replicate g.length jtok ++ [jdelim]) := by
  simp [cntReg, List.reverse_cons, List.map_append, List.flatten_append]

theorem outGlyphs_nil_left (Gs : List (List Glyph)) : outGlyphs [] Gs = [Glyph.nil] := by
  simp [outGlyphs]

@[simp] theorem outGlyphs_nil_right (Ws : List (List Glyph)) : outGlyphs Ws [] = [Glyph.nil] := by
  simp [outGlyphs]

theorem outGlyphs_cons (w g : List Glyph) (Ws Gs : List (List Glyph)) :
    outGlyphs (w :: Ws) (g :: Gs) =
      ([Glyph.cons, Glyph.cons] ++ w ++ g) ++ outGlyphs Ws Gs := by
  simp [outGlyphs, List.zipWith_cons_cons]

/-- `listEncR` is the encoding of `ofList`. -/
theorem listEncR_map_enc (xs : List Val) : (ofList xs).enc = listEncR (xs.map Val.enc) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      rw [show ofList (x :: xs) = Val.cons x (ofList xs) from rfl, Val.enc, ih]
      simp [listEncR, List.map_cons, List.flatten_cons, List.cons_append]

end Work.MainP
