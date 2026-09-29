import Mathlib
import Submission.Work.IntLib.evDefs
import Submission.Work.IntLib.chunkDefs
import Submission.Work.IntLib.Shift.Base
import Submission.Work.Layout.Base
import Submission.Work.IntLib.cmpWord

/-!
# `Work.IntLib.evReadValue`: reading a value off stack 0, reversed, onto stack `k`

`evReadValue` is the elementary "value reader" of the `IntLib`: a *main*-independent program which,
whenever the top value of stack 0 is `int h`, removes it from stack 0 (leaving the caller's
remainder `rest` in place) and pushes its whole encoding, **reversed**, on top of the caller's data
on any other stack `k ≠ 0`.  The cost is linear in the size of the value, `K * (h.size + 2)`, and
every other stack is untouched.

The program is the transfer loop `Cmp.tLoop 0 Glyph.iend k 0` of `Submission/Work/IntLib/cmpWord`
(which moves every glyph above the closing `iend` of the encoding onto stack `k`, reversing it),
followed by one `pop`/`push` pair which transfers the `iend` itself.  Reading the encoding

`Val.enc (.int (h : ℤ)) = pos :: (encodeNat h).map bit ++ [iend]`

from the top, the loop consumes exactly the `h.size + 2` glyphs of the value, so the cost bound
`7 * (h.size + 2)` follows from `encodeNat_length`.
-/

set_option autoImplicit false

namespace Work.IntLib

open HvdH

/-- The read-value word: the whole encoding of the integer on top of stack 0 is moved to stack `k`,
reversed, above whatever `k` already carried; stack 0 is left with the caller's `rest`, and all
other stacks are unchanged.  The transfer itself is `Cmp.tLoop 0 iend k 0` (reverse everything above
the closing `iend`), plus one `pop`/`push` pair for the `iend`.

Cost: `5 * (h.size + 1) + 7 + 1 + 1 = 5 * h.size + 14 ≤ 7 * (h.size + 2)`. -/
theorem evReadValue (k : HvdH.Stk) (hk : k ≠ (0 : HvdH.Stk)) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (g : HvdH.Reg → HvdH.Glyph)
      (X : HvdH.Stk → List HvdH.Glyph) (h : ℕ) (rest : List HvdH.Glyph),
      X 0 = HvdH.Val.enc (.int (h : ℤ)) ++ rest →
      ∃ (s' : HvdH.State) (n : ℕ), Work.Layout.Ev main prog ⟨g, X⟩ s' n ∧
        n ≤ K * (h.size + 2) ∧
        s'.stk 0 = rest ∧
        s'.stk k = (HvdH.Val.enc (.int (h : ℤ))).reverse ++ X k ∧
        (∀ j : HvdH.Stk, j ≠ 0 → j ≠ k → s'.stk j = X j) := by
  refine ⟨.seq (Cmp.tLoop (0 : Stk) Glyph.iend k (0 : Reg))
    (.seq (.pop (0 : Stk) (0 : Reg)) (.push k (0 : Reg))), 7, ?_⟩
  intro main g X h rest hX
  -- the glyphs of the value which lie above its closing `iend`
  set gs : List Glyph := Glyph.pos :: (Computability.encodeNat h).map Glyph.bit with hgs
  have hgt : ¬ ((h : ℤ) < 0) := by
    have h0 : (0 : ℤ) ≤ (h : ℤ) := Int.ofNat_nonneg h
    omega
  have henc : HvdH.Val.enc (.int (h : ℤ)) = gs ++ [Glyph.iend] := by
    rw [hgs, enc_int, if_neg hgt]
    rfl
  have hglen : gs.length = h.size + 1 := by
    rw [hgs, List.length_cons, List.length_map, encodeNat_length]
  have hX' : X (0 : Stk) = gs ++ Glyph.iend :: rest := by
    rw [hX, henc]
    simp
  -- none of those glyphs is the closing `iend`
  have hT : ∀ gg ∈ gs, gg ≠ Glyph.iend := by
    intro gg hgg
    rw [hgs] at hgg
    rcases List.mem_cons.mp hgg with hh | hmem
    · rw [hh]; intro hc; cases hc
    · obtain ⟨b, -, hb⟩ := List.mem_map.mp hmem
      rw [← hb]; intro hc; cases hc
  -- the transfer loop
  set s1 : State := Cmp.tSt (0 : Stk) Glyph.iend k (0 : Reg) gs rest ⟨g, X⟩ with hs1
  have e1 : Eval main (Cmp.tLoop (0 : Stk) Glyph.iend k (0 : Reg)) ⟨g, X⟩ s1
      (5 * gs.length + 7) := by
    rw [hs1]
    exact Cmp.tLoop_eval main (0 : Stk) Glyph.iend k (0 : Reg) hk (by decide) gs rest ⟨g, X⟩ hX' hT
  have h1s0 : s1.stk (0 : Stk) = Glyph.iend :: rest := by
    rw [hs1]
    exact Cmp.tSt_stk_k (0 : Stk) Glyph.iend k (0 : Reg) gs rest ⟨g, X⟩ hk
  have h1sk : s1.stk k = gs.reverse ++ X k := by
    rw [hs1]
    exact Cmp.tSt_stk_dst (0 : Stk) Glyph.iend k (0 : Reg) gs rest ⟨g, X⟩
  have h1oth : ∀ j : Stk, j ≠ (0 : Stk) → j ≠ k → s1.stk j = X j := by
    intro j hj0 hjk
    rw [hs1]
    exact Cmp.tSt_stk_ne (0 : Stk) Glyph.iend k (0 : Reg) gs rest ⟨g, X⟩ hj0 hjk
  -- pop the `iend`
  set s2 : State := ⟨Function.update s1.reg (0 : Reg) ((s1.stk (0 : Stk)).headD Glyph.eos),
      Function.update s1.stk (0 : Stk) (s1.stk (0 : Stk)).tail⟩ with hs2
  have e2 : Eval main (.pop (0 : Stk) (0 : Reg)) s1 s2 1 := by
    rw [hs2]
    exact Eval.pop (0 : Stk) (0 : Reg) s1
  have h2s0 : s2.stk (0 : Stk) = rest := by
    rw [hs2]
    show (Function.update s1.stk (0 : Stk) (s1.stk (0 : Stk)).tail) (0 : Stk) = rest
    rw [Function.update_self, h1s0]
    rfl
  have h2reg : s2.reg (0 : Reg) = Glyph.iend := by
    rw [hs2]
    show (Function.update s1.reg (0 : Reg) ((s1.stk (0 : Stk)).headD Glyph.eos)) (0 : Reg)
      = Glyph.iend
    rw [Function.update_self, h1s0]
    rfl
  have h2sk : s2.stk k = gs.reverse ++ X k := by
    rw [hs2]
    show (Function.update s1.stk (0 : Stk) (s1.stk (0 : Stk)).tail) k = gs.reverse ++ X k
    rw [Function.update_of_ne hk, h1sk]
  have h2oth : ∀ j : Stk, j ≠ (0 : Stk) → j ≠ k → s2.stk j = X j := by
    intro j hj0 hjk
    rw [hs2]
    show (Function.update s1.stk (0 : Stk) (s1.stk (0 : Stk)).tail) j = X j
    rw [Function.update_of_ne hj0]
    exact h1oth j hj0 hjk
  -- push it onto stack `k`
  set s3 : State := ⟨s2.reg, Function.update s2.stk k (s2.reg (0 : Reg) :: s2.stk k)⟩ with hs3
  have e3 : Eval main (.push k (0 : Reg)) s2 s3 1 := by
    rw [hs3]
    exact Eval.push k (0 : Reg) s2
  have e23 : Eval main (.seq (.pop (0 : Stk) (0 : Reg)) (.push k (0 : Reg))) s1 s3 2 :=
    Eval.seq e2 e3
  have eall : Eval main (.seq (Cmp.tLoop (0 : Stk) Glyph.iend k (0 : Reg))
      (.seq (.pop (0 : Stk) (0 : Reg)) (.push k (0 : Reg)))) ⟨g, X⟩ s3
      ((5 * gs.length + 7) + 2) := Eval.seq e1 e23
  refine ⟨s3, 5 * gs.length + 7 + 1 + 1, ⟨5 * gs.length + 7 + 1 + 1, eall, le_rfl⟩,
    ?_, ?_, ?_, ?_⟩
  · rw [hglen]
    omega
  · rw [hs3]
    show (Function.update s2.stk k (s2.reg (0 : Reg) :: s2.stk k)) (0 : Stk) = rest
    rw [Function.update_of_ne (Ne.symm hk), h2s0]
  · rw [hs3]
    show (Function.update s2.stk k (s2.reg (0 : Reg) :: s2.stk k)) k
      = (HvdH.Val.enc (.int (h : ℤ))).reverse ++ X k
    rw [Function.update_self, h2reg, h2sk, henc]
    simp
  · intro j hj0 hjk
    rw [hs3]
    show (Function.update s2.stk k (s2.reg (0 : Reg) :: s2.stk k)) j = X j
    rw [Function.update_of_ne hjk]
    exact h2oth j hj0 hjk

end Work.IntLib
