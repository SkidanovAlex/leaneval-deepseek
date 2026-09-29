import Mathlib
import Submission.Work.Layout.AA.Defs

/-!
# `prependTo`: `Ev`-level specification

`Work.Layout.prependTo a b c d rr` moves the top value `v` of stack `a` on top of the value of
stack `b` and wraps it there in a fresh `cons` cell, i.e. it replaces the value `ofList L` of `b`
by `ofList (v :: L)`.

It is the composition of `Work.Layout.mvVal` (move one value from `a` to `b`, normal order, using
`c` and `d` as scratch) with `Work.Kernel.pushGlyphs` (push the single glyph `cons` on `b`).

The specification below is the `Ev`-level statement of `Work.Layout.mvVal_ev`
(`Submission/Work/Layout/Move.lean`) followed by the `pushGlyphs` evaluation lemma
(`Submission/Work/Kernel/Raw.lean`); the cost is `16 * (vsz v + 1) + 3`, bounded by the stated
`20 * (vsz v + 1) + 4`.
-/

set_option autoImplicit false

namespace Work.Layout.AA

open HvdH

/-- `prependTo` moves the top value of `a` onto the front of the value list of `b`: the value
`ofList L` on `b` becomes `ofList (v :: L)`.  Cost `≤ 20 * (vsz v + 1) + 4`; only stacks `a`,
`b`, `c`, `d` are touched. -/
theorem prependTo_ev (main : HvdH.Cmd) (a b c d : HvdH.Stk) (rr : HvdH.Reg)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph) (v : HvdH.Val)
    (L : List HvdH.Val) (A B : List HvdH.Glyph) (ha : X a = v.enc ++ A)
    (hb : X b = (HvdH.ofList L).enc ++ B) :
    ∃ s' n, Work.Layout.Ev main (Work.Layout.prependTo a b c d rr) ⟨g, X⟩ s' n ∧
      n ≤ 20 * (HvdH.vsz v + 1) + 4 ∧ s'.stk a = A ∧
      s'.stk b = (HvdH.ofList (v :: L)).enc ++ B ∧
      (∀ j, j ≠ a → j ≠ b → j ≠ c → j ≠ d → s'.stk j = X j) := by
  -- step 1: move the value `v` from `a` to `b`
  obtain ⟨s₁, n₁, hev₁, hn₁, ha₁, hb₁, hf₁⟩ :=
    Work.Layout.mvVal_ev (main := main) hab hac had hbc hbd hcd (g := g) (X := X)
      (v := v) (A := A) (B := (HvdH.ofList L).enc ++ B) ha hb
  -- step 2: push the `cons` cell on `b`
  have hpush : Work.Layout.Ev main (Work.Kernel.pushGlyphs [HvdH.Glyph.cons] b rr) s₁
      (Work.Kernel.pushGlyphsState [HvdH.Glyph.cons] b rr s₁) 3 :=
    ⟨_, Work.Kernel.eval_pushGlyphs main [HvdH.Glyph.cons] b rr s₁, by decide⟩
  have hmain : Work.Layout.Ev main (Work.Layout.prependTo a b c d rr) ⟨g, X⟩
      (Work.Kernel.pushGlyphsState [HvdH.Glyph.cons] b rr s₁) (n₁ + 3) := by
    unfold Work.Layout.prependTo
    exact Work.Layout.Ev.seq hev₁ hpush
  refine ⟨_, _, hmain, ?_, ?_, ?_, ?_⟩
  · -- cost
    have h₁ : n₁ ≤ 16 * (HvdH.vsz v + 1) := hn₁
    omega
  · -- stack `a` keeps its tail
    rw [Work.Kernel.pushGlyphsState_stk, if_neg hab]
    exact ha₁
  · -- stack `b` gains a `cons` cell in front of `v.enc`
    rw [Work.Kernel.pushGlyphsState_stk, if_pos rfl, hb₁,
      show (HvdH.ofList (v :: L)).enc = HvdH.Glyph.cons :: (v.enc ++ (HvdH.ofList L).enc) from rfl]
    simp [List.append_assoc]
  · -- frame
    intro j hja hjb hjc hjd
    rw [Work.Kernel.pushGlyphsState_stk, if_neg hjb]
    exact hf₁ j hja hjb hjc hjd

end Work.Layout.AA
