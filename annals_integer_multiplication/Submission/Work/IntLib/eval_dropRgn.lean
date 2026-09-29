import Mathlib
import Submission.Work.IntLib.divRaw

namespace Work.IntLib

open HvdH

theorem eval_dropRgn (main : HvdH.Cmd) (k : HvdH.Stk) (T : HvdH.Glyph) (r : HvdH.Reg)
    (l bk : List HvdH.Glyph) (s : HvdH.State) (hT : ∀ g ∈ l, g ≠ T)
    (hk : s.stk k = l ++ T :: bk) :
    ∃ s' n, HvdH.Eval main (Work.IntLib.dropRgn k T r) s s' n ∧ n ≤ 6 * (l.length + 1) + 9 ∧
      s'.stk k = bk ∧ ∀ j : HvdH.Stk, j ≠ k → s'.stk j = s.stk j := by
  let Inv : List HvdH.Glyph → HvdH.State → Prop :=
    fun gs t => t.stk k = gs ++ T :: bk ∧ (∀ g ∈ gs, g ≠ T) ∧
      ∀ j : HvdH.Stk, j ≠ k → t.stk j = s.stk j
  have hstk : ∀ gs t, Inv gs t → t.stk k = gs ++ T :: bk := fun gs t h => h.1
  have hterm : ∀ (g : HvdH.Glyph) (gs : List HvdH.Glyph) (t : HvdH.State),
      Inv (g :: gs) t → g ≠ T := by
    intro g gs t h
    exact h.2.1 g (by simp)
  have hreg : ∀ gs t (g : HvdH.Glyph), Inv gs t →
      Inv gs ⟨Function.update t.reg r g, t.stk⟩ := by
    intro gs t g h
    exact ⟨h.1, h.2.1, fun j hj => h.2.2 j hj⟩
  have hpop : ∀ (g : HvdH.Glyph) (gs : List HvdH.Glyph) (t : HvdH.State),
      Inv (g :: gs) t →
      Inv gs ⟨Function.update t.reg r g, Function.update t.stk k (gs ++ T :: bk)⟩ := by
    intro g gs t h
    refine ⟨by simp, ?_, ?_⟩
    · intro x hx
      exact h.2.1 x (List.mem_cons_of_mem g hx)
    · intro j hj
      simp [Function.update_of_ne hj, h.2.2 j hj]
  have hstep : ∀ (g : HvdH.Glyph) (gs : List HvdH.Glyph) (t : HvdH.State),
      g ≠ T → t.reg r = g → Inv gs t →
      ∃ t' n, HvdH.Eval main HvdH.Cmd.skip t t' n ∧ n ≤ 1 ∧ Inv gs t' := by
    intro g gs t _ _ h
    exact ⟨t, 1, Eval.skip t, le_refl 1, h⟩
  have hIns : Inv l s := ⟨hk, hT, fun j _ => rfl⟩
  obtain ⟨s', n, hev, hinv, hne, hn⟩ :=
    consume_eval (main := main) (k := k) (T := T) (r := r) (handler := HvdH.Cmd.skip)
      (Inv := Inv) (below := bk) (b := 1) hstk hterm hreg hpop hstep l s hIns
  have hsk' : s'.stk k = T :: bk := by
    have h1 := hinv.1
    simpa using h1
  have hfr : ∀ j : HvdH.Stk, j ≠ k → s'.stk j = s.stk j := fun j hj => hinv.2.2 j hj
  refine ⟨⟨Function.update s'.reg r T, Function.update s'.stk k bk⟩, n + 1, ?_, ?_, ?_, ?_⟩
  · have hpop' : HvdH.Eval main (HvdH.Cmd.pop k r) s'
        ⟨Function.update s'.reg r T, Function.update s'.stk k bk⟩ 1 :=
      Eval.pop_cons hsk'
    have hseq := Eval.seq hev hpop'
    simpa [Work.IntLib.dropRgn] using hseq
  · have hb : (l.length + 1) * 5 + 7 = (l.length + 1) * (1 + 4) + 7 := by ring
    omega
  · simp
  · intro j hj
    simp [Function.update_of_ne hj, hfr j hj]

end Work.IntLib
