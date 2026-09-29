import Mathlib
import Submission.Work.IntLib.divRaw
import Submission.Work.IntLib.eval_mvRevOnto

/-!
# `incBitsFinal` in the "bit `false`" case (area IntLib)

`Work.IntLib.incBitsFinal k T S rr rs` is the final step of the `incBits` carry propagation: the
carry loop has just peeked the first glyph of the region `bitsG l ++ T :: bk` of stack `k` that is
not a `true` bit (or the marker `T`, when every bit was `true`), and this command
* pops that glyph (it is a `false` bit),
* pushes the carry `true` onto the scratch stack `S`,
* moves the remaining bits of the region onto `S` (reversed), leaving the marker `T` on top of `k`,
* drops `T`.

The lemma below specifies the case in which the peeked glyph is indeed `false`.  The movement of the
remaining bits is exactly the `consume_push_rev` loop already proved in
`Submission/Work/IntLib/eval_mvRevOnto.lean` (cost `≤ 5 * l.length + 8`), so the total cost is
`1 + 1 + 1 + 1 + (5 * r.length + 8) + 1 = 5 * r.length + 13 ≤ 5 * r.length + 14`.
-/

set_option autoImplicit false

namespace Work.IntLib

open HvdH

/-- A list of glyphs of the form `bitsG r` never contains the marker `T` (which is not a bit). -/
theorem bitsG_ne_of_bit_ne {r : List Bool} {T : Glyph} (hT : ∀ b : Bool, Glyph.bit b ≠ T) :
    ∀ g ∈ bitsG r, g ≠ T := by
  intro g hg
  obtain ⟨b, -, hb⟩ := List.mem_map.mp hg
  rw [← hb]
  exact hT b

theorem incBitsFinal_eval_false (main : HvdH.Cmd) (k : HvdH.Stk) (T : HvdH.Glyph) (S : HvdH.Stk)
    (rr rs : HvdH.Reg) (r : List Bool) (bk : List HvdH.Glyph) (Scont : List HvdH.Glyph)
    (s : HvdH.State) (hT : ∀ b : Bool, HvdH.Glyph.bit b ≠ T) (hne : k ≠ S)
    (hk : s.stk k = HvdH.Glyph.bit false :: (Work.IntLib.bitsG r ++ T :: bk))
    (hS : s.stk S = Scont) (hreg : s.reg rr = HvdH.Glyph.bit false) :
    ∃ s' n, HvdH.Eval main (Work.IntLib.incBitsFinal k T S rr rs) s s' n ∧
      n ≤ 5 * r.length + 14 ∧
      s'.stk k = bk ∧
      s'.stk S = (Work.IntLib.bitsG r).reverse ++ HvdH.Glyph.bit true :: Scont ∧
      ∀ j : HvdH.Stk, j ≠ k → j ≠ S → s'.stk j = s.stk j := by
  have hTmem : ∀ g ∈ bitsG r, g ≠ T := bitsG_ne_of_bit_ne hT
  -- step 1: `pop k rr` removes the low bit `false`
  set s1 : State := ⟨Function.update s.reg rr (Glyph.bit false),
    Function.update s.stk k (bitsG r ++ T :: bk)⟩ with hs1
  have e1 : Eval main (.pop k rr) s s1 1 := by
    rw [hs1]; exact Eval.pop_cons hk
  -- step 2: `set rs (bit true)`
  set s2 : State := ⟨Function.update s1.reg rs (Glyph.bit true), s1.stk⟩ with hs2
  have e2 : Eval main (.set rs (Glyph.bit true)) s1 s2 1 := by
    rw [hs2]; exact Eval.set rs (Glyph.bit true) s1
  -- step 3: `push S rs` pushes the carry `true` on the scratch stack
  set s3 : State := ⟨s2.reg, Function.update s2.stk S (Glyph.bit true :: Scont)⟩ with hs3
  have e3 : Eval main (.push S rs) s2 s3 1 := by
    rw [hs3]
    have h := Eval.push (main := main) S rs s2
    have hr : s2.reg rs = Glyph.bit true := by
      show Function.update s1.reg rs (Glyph.bit true) rs = Glyph.bit true
      rw [Function.update_self]
    have hSk : s2.stk S = Scont := by
      show Function.update s.stk k (bitsG r ++ T :: bk) S = Scont
      rw [Function.update_of_ne (Ne.symm hne), hS]
    simpa [hr, hSk] using h
  -- step 4: `consume k T rs (.push S rs)` moves the remaining bits onto `S`, reversed
  have hk3 : s3.stk k = bitsG r ++ T :: bk := by
    show Function.update (Function.update s.stk k (bitsG r ++ T :: bk)) S
      (Glyph.bit true :: Scont) k = bitsG r ++ T :: bk
    rw [Function.update_of_ne hne, Function.update_self]
  have hS3 : s3.stk S = Glyph.bit true :: Scont := by
    show Function.update (Function.update s.stk k (bitsG r ++ T :: bk)) S
      (Glyph.bit true :: Scont) S = Glyph.bit true :: Scont
    rw [Function.update_self]
  obtain ⟨s4, n4, hev4, hn4, h4k, h4S, h4fr⟩ :=
    consume_push_rev main k T S rs (bitsG r) bk (Glyph.bit true :: Scont)
      hne hTmem s3 hk3 hS3
  -- step 5: `pop k rs` drops the frame marker `T` of stack `k`
  set s5 : State := ⟨Function.update s4.reg rs T, Function.update s4.stk k bk⟩ with hs5
  have e5 : Eval main (.pop k rs) s4 s5 1 := by
    rw [hs5]; exact Eval.pop_cons h4k
  have eall : Eval main (incBitsFinal k T S rr rs) s s5
      ((1 + (1 + (1 + (n4 + 1)))) + 1) :=
    Eval.iteT hreg (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq hev4 e5))))
  refine ⟨s5, (1 + (1 + (1 + (n4 + 1)))) + 1, eall, ?_, ?_, ?_, ?_⟩
  · have hlen : (bitsG r).length = r.length := by simp [bitsG]
    omega
  · show Function.update s4.stk k bk k = bk
    rw [Function.update_self]
  · show Function.update s4.stk k bk S = (bitsG r).reverse ++ Glyph.bit true :: Scont
    rw [Function.update_of_ne (Ne.symm hne)]
    exact h4S
  · intro j hjk hjS
    show Function.update s4.stk k bk j = s.stk j
    rw [Function.update_of_ne hjk, h4fr j hjk hjS]
    show Function.update (Function.update s.stk k (bitsG r ++ T :: bk)) S
      (Glyph.bit true :: Scont) j = s.stk j
    rw [Function.update_of_ne hjS, Function.update_of_ne hjk]

end Work.IntLib
