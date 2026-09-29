import Mathlib
import Submission.Work.Kernel.zipWithDefs

set_option autoImplicit false

namespace Work.Kernel

open HvdH

/-- One iteration of the rebuild loop of `zipWith` in the *miss* case: the top glyph of stack 3 is
not the boundary marker, so `zipWith_rebuildBody` moves the value `v` sitting on top of stack 3 down
to stack 0, pushes a `cons` glyph on top of it, and resets the loop flag to `cons`.

Cost: `1` (`peek`) `+ 1` (`ite` test) `+ 16 * (vsz v + 1)` (`mvVal`) `+ 2` (`pushConst`) `+ 1`
(`set`) `= 16 * (vsz v + 1) + 5`. -/
theorem zipWith_rebuildBody_miss (main : HvdH.Cmd) {s : HvdH.State} {v : HvdH.Val}
    {A : List HvdH.Glyph} (h3 : s.stk 3 = v.enc ++ A)
    (hhead : (v.enc ++ A).headD HvdH.Glyph.eos ≠ Work.Layout.gMark) :
    ∃ s' n, HvdH.Eval main Work.Kernel.zipWith_rebuildBody s s' n ∧
      n ≤ 16 * (HvdH.vsz v + 1) + 5 ∧ s'.stk 3 = A ∧
      s'.stk 0 = HvdH.Glyph.cons :: (v.enc ++ s.stk 0) ∧
      s'.reg Work.Layout.rLoopG = HvdH.Glyph.cons ∧
      (∀ j, j ≠ 0 → j ≠ 3 → s'.stk j = s.stk j) := by
  -- the test of the `ite`: peek stack 3 into `rA`; the result is the head of `v.enc ++ A`, a
  -- non-marker glyph, so the "miss" branch is taken
  have hpeek : Work.Layout.Ev main (.peek (3 : Stk) Work.Layout.rA) s
      ⟨Function.update s.reg Work.Layout.rA ((s.stk 3).headD .eos), s.stk⟩ 1 :=
    Work.Layout.ev_peek main 3 Work.Layout.rA s
  have hne :
      (⟨Function.update s.reg Work.Layout.rA ((s.stk 3).headD .eos), s.stk⟩ : State).reg
        Work.Layout.rA ≠ Work.Layout.gMark := by
    simp only [Function.update_self]
    rw [h3]
    exact hhead
  -- move the value `v` from stack 3 to the value stack
  obtain ⟨s1, n1, hmv, hn1, h1_3, h1_0, h1_4, h1_5, h1_fr⟩ :=
    Work.Layout.mvVal_ev_full (main := main) (a := (3 : Stk)) (b := (0 : Stk)) (c := (4 : Stk))
      (d := (5 : Stk)) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := Function.update s.reg Work.Layout.rA ((s.stk 3).headD .eos)) (X := s.stk)
      (v := v) (A := A) (B := s.stk 0) h3 rfl
  -- push the `cons` glyph on top of it
  obtain ⟨s2, n2, hpush, hn2, h2_0, h2_fr, -, -⟩ :=
    Work.Layout.pushConst_ev (main := main) (k := (0 : Stk)) (cst := Glyph.cons)
      (g := s1.reg) (X := s1.stk)
  -- reset the loop flag
  have hset : Work.Layout.Ev main (.set Work.Layout.rLoopG Glyph.cons) s2
      (State.tSet s2 Work.Layout.rLoopG Glyph.cons) 1 :=
    Work.Layout.ev_set main Work.Layout.rLoopG Glyph.cons s2
  -- assemble the whole run (with the budget `16 * (vsz v + 1) + 5`)
  have hbody : Work.Layout.Ev main zipWith_rebuildBody s
      (State.tSet s2 Work.Layout.rLoopG Glyph.cons) (16 * (vsz v + 1) + 5) :=
    (Work.Layout.Ev.seq hpeek
      (Work.Layout.Ev.iteF hne
        (Work.Layout.Ev.seq hmv (Work.Layout.Ev.seq hpush hset)))).mono (by omega)
  obtain ⟨n, heval, hnle⟩ := hbody
  refine ⟨State.tSet s2 Work.Layout.rLoopG Glyph.cons, n, heval, hnle, ?_, ?_, ?_, ?_⟩
  · show s2.stk 3 = A
    rw [h2_fr 3 (by decide), h1_3]
  · show s2.stk 0 = Glyph.cons :: (v.enc ++ s.stk 0)
    rw [h2_0, h1_0]
  · simp [State.tSet, State.updReg]
  · intro j hj0 hj3
    show s2.stk j = s.stk j
    rcases eq_or_ne j (4 : Stk) with h4 | h4
    · rw [h4, h2_fr 4 (by decide), h1_4]
    · rcases eq_or_ne j (5 : Stk) with h5 | h5
      · rw [h5, h2_fr 5 (by decide), h1_5]
      · rw [h2_fr j hj0, h1_fr j hj3 hj0 h4 h5]

end Work.Kernel
