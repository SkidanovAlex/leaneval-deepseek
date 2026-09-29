import Mathlib
import Submission.Work.Layout.AA.ProgAux

namespace Work.SynFFT

/-- `Work.Layout.prependTo a b c d rr` moves the top value `v` of stack `a` onto the front of the
value list of stack `b` (`ofList L ↦ ofList (v :: L)`), restoring *all* other stacks exactly,
including the two scratch stacks `c` and `d`, at cost `≤ 20 * (vsz v + 1) + 4`.

This is `Work.Layout.AA.prependTo_ev` with the scratch stacks `c`, `d` recovered from the
full-strength one-value mover `Work.Layout.AA.mvVal_ev'`. -/
theorem prependToScratchEv (main : HvdH.Cmd) (a b c d : HvdH.Stk) (rr : HvdH.Reg)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph) (v : HvdH.Val)
    (L : List HvdH.Val) (A B : List HvdH.Glyph) (ha : X a = v.enc ++ A)
    (hb : X b = (HvdH.ofList L).enc ++ B) :
    ∃ s' n, Work.Layout.Ev main (Work.Layout.prependTo a b c d rr) ⟨g, X⟩ s' n ∧
      n ≤ 20 * (HvdH.vsz v + 1) + 4 ∧ s'.stk a = A ∧
      s'.stk b = (HvdH.ofList (v :: L)).enc ++ B ∧ s'.stk c = X c ∧ s'.stk d = X d ∧
      (∀ j, j ≠ a → j ≠ b → s'.stk j = X j) := by
  -- step 1: move the value `v` from `a` to `b`, restoring the scratch stacks `c`, `d`
  obtain ⟨s₁, n₁, hev₁, hn₁, ha₁, hb₁, hc₁, hd₁, hf₁⟩ :=
    Work.Layout.AA.mvVal_ev' (main := main) hab hac had hbc hbd hcd (g := g) (X := X)
      (v := v) (A := A) (B := (HvdH.ofList L).enc ++ B) ha hb
  -- step 2: push the `cons` cell on `b` (touches only stack `b`)
  have hpush : Work.Layout.Ev main (Work.Kernel.pushGlyphs [HvdH.Glyph.cons] b rr) s₁
      (Work.Kernel.pushGlyphsState [HvdH.Glyph.cons] b rr s₁) 3 :=
    ⟨_, Work.Kernel.eval_pushGlyphs main [HvdH.Glyph.cons] b rr s₁, by decide⟩
  have hmain : Work.Layout.Ev main (Work.Layout.prependTo a b c d rr) ⟨g, X⟩
      (Work.Kernel.pushGlyphsState [HvdH.Glyph.cons] b rr s₁) (n₁ + 3) := by
    unfold Work.Layout.prependTo
    exact Work.Layout.Ev.seq hev₁ hpush
  refine ⟨_, _, hmain, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- cost
    have h₁ : n₁ ≤ 16 * (HvdH.vsz v + 1) := hn₁
    omega
  · -- stack `a` keeps its tail
    rw [Work.Kernel.pushGlyphsState_stk, if_neg hab, ha₁]
  · -- stack `b` gains a `cons` cell in front of `v.enc`
    rw [Work.Kernel.pushGlyphsState_stk, if_pos rfl, hb₁,
      show (HvdH.ofList (v :: L)).enc = HvdH.Glyph.cons :: (v.enc ++ (HvdH.ofList L).enc) from rfl]
    simp [List.append_assoc]
  · -- stack `c` restored
    rw [Work.Kernel.pushGlyphsState_stk, if_neg (Ne.symm hbc), hc₁]
  · -- stack `d` restored
    rw [Work.Kernel.pushGlyphsState_stk, if_neg (Ne.symm hbd), hd₁]
  · -- frame
    intro j hja hjb
    rw [Work.Kernel.pushGlyphsState_stk, if_neg hjb]
    exact hf₁ j hja hjb

end Work.SynFFT
