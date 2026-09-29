import Mathlib
import Submission.Work.IntLib.parseEmitDefs
import Submission.Work.Kernel.Raw

/-!
# `splitLoopEval`: the splitting scan of the `parse` word

`Work.IntLib.splitLoop r` is the scan that empties the raw-input stack 0, dispatching each glyph
with `Work.IntLib.splitCmd r` (which pushes the bits of an input symbol on the accumulators 1 and 2)
and stopping as soon as it pops an `eos`, i.e. as soon as stack 0 is empty.

`Work.IntLib.splitLoopEval` is the local correctness statement of that loop, in the "branch
hypothesis + invariant" style used throughout the `IntLib` development:

* `hbranch` is the (checked once, by `splitGlyphEval`) effect of one dispatch step: for every
  non-`eos` glyph `g` sitting in register `r`, `splitCmd r ;;; set r eos` runs in at most `b` steps,
  prepends `inX g` / `inY g` to the accumulators and restores everything else;
* the theorem then scans a whole list `gs` (all glyphs non-`eos`) off stack 0 and concludes that
  the scan terminates in `(gs.length + 1) * (b + 4) + 1` steps with stack 0 empty, the accumulators
  holding `pushAcc inX gs.reverse` / `pushAcc inY gs.reverse` above their initial contents, and the
  register `r` holding `mk 15` (in particular `≠ eos`, so that the caller knows the loop is over).

The cost is proved simultaneously with the correctness: each iteration costs `n + 2 ≤ b + 2` for the
body plus one for the loop test, and there is one extra final iteration (cost 3 plus a failing test)
in which the empty stack 0 is popped; hence `gs.length * (b + 3) + 5` steps, comfortably inside the
advertised `(gs.length + 1) * (b + 4) + 1`.
-/

set_option autoImplicit false

namespace Work.IntLib

open HvdH
open Work.Kernel

/-- `pushAcc` is additive in the list argument: the conjugates of `l₁ ++ l₂` on a stack are the
conjugates of `l₁` on top of those of `l₂`. -/
private theorem pushAcc_append (f : Glyph → List Glyph) (l₁ l₂ : List Glyph) :
    pushAcc f (l₁ ++ l₂) = pushAcc f l₁ ++ pushAcc f l₂ := by
  induction l₁ with
  | nil => simp
  | cons g t ih => simp [ih, List.append_assoc]

/-- One iteration of `splitBody r` in which the popped glyph is `eos` (stack 0 empty): the test
register is set to `mk 15` and the loop will stop. Cost 3 (`pop`, `ite` test, `set`). -/
private theorem eval_splitBody_exit (main : Cmd) (r : Reg) (Y : State)
    (h : (State.tPop Y 0 r).reg r = Glyph.eos) :
    Eval main (splitBody r) Y (State.tSet (State.tPop Y 0 r) r (Glyph.mk 15)) 3 := by
  have h1 : Eval main (.pop 0 r) Y (State.tPop Y 0 r) 1 := eval_pop main 0 r Y
  have h2 : Eval main (.set r (Glyph.mk 15)) (State.tPop Y 0 r)
      (State.tSet (State.tPop Y 0 r) r (Glyph.mk 15)) 1 := eval_set main r (Glyph.mk 15) _
  have h3 : Eval main (.ite r Glyph.eos (.set r (Glyph.mk 15)) (.seq (splitCmd r) (.set r Glyph.eos)))
      (State.tPop Y 0 r) (State.tSet (State.tPop Y 0 r) r (Glyph.mk 15)) (1 + 1) :=
    eval_iteT h h2
  have h4 : Eval main (splitBody r) Y (State.tSet (State.tPop Y 0 r) r (Glyph.mk 15)) (1 + (1 + 1)) := by
    simpa [splitBody] using eval_seq h1 h3
  simpa using h4

/-- One iteration of `splitBody r` in which the popped glyph `g` is not `eos`: the `else` branch
`splitCmd r ;;; set r eos` is run. If that branch costs `n`, the iteration costs `n + 2`. -/
private theorem eval_splitBody_step (main : Cmd) (r : Reg) (Y : State) {Y2 : State} {n : ℕ}
    (h : (State.tPop Y 0 r).reg r ≠ Glyph.eos)
    (hb : Eval main (.seq (splitCmd r) (.set r Glyph.eos)) (State.tPop Y 0 r) Y2 n) :
    Eval main (splitBody r) Y Y2 (n + 2) := by
  have h1 : Eval main (.pop 0 r) Y (State.tPop Y 0 r) 1 := eval_pop main 0 r Y
  have h2 : Eval main (.ite r Glyph.eos (.set r (Glyph.mk 15)) (.seq (splitCmd r) (.set r Glyph.eos)))
      (State.tPop Y 0 r) Y2 (n + 1) := eval_iteF h hb
  have h3 : Eval main
      (.seq (.pop 0 r) (.ite r Glyph.eos (.set r (Glyph.mk 15)) (.seq (splitCmd r) (.set r Glyph.eos))))
      Y Y2 (1 + (n + 1)) := eval_seq h1 h2
  have hc : 1 + (n + 1) = n + 2 := by omega
  simpa [splitBody, hc] using h3

/-- The induction underlying `splitLoopEval`: running `splitLoop r` from a state whose stack 0 is
`gs` (all glyphs non-`eos`) and whose test register is `eos` empties stack 0 (and stops) after
`gs.length * (b + 3) + 5` steps, having conjugated `gs` onto the two accumulators. The two
accumulator stacks enter through the "initial content" list `pre` (already-consumed glyphs, most
recent first) and the reference state `s` describing the untouched stacks. -/
private theorem splitLoop_aux (main : Cmd) (r : Reg) (b : ℕ)
    (hbranch : ∀ (g : Glyph) (Y : State), g ≠ Glyph.eos → Y.reg r = g →
      ∃ (Y' : State) (n : ℕ), n ≤ b ∧
        Eval main (Cmd.seq (splitCmd r) (Cmd.set r Glyph.eos)) Y Y' n ∧
        Y'.stk 0 = Y.stk 0 ∧ Y'.stk 1 = inX g ++ Y.stk 1 ∧
        Y'.stk 2 = inY g ++ Y.stk 2 ∧ Y'.reg r = Glyph.eos ∧
        (∀ j : Stk, j ≠ 0 → j ≠ 1 → j ≠ 2 → Y'.stk j = Y.stk j)) :
    ∀ (gs : List Glyph) (pre : List Glyph) (s Y : State), (∀ g ∈ gs, g ≠ Glyph.eos) →
      Y.stk 0 = gs → Y.reg r = Glyph.eos →
      Y.stk 1 = pushAcc inX pre ++ s.stk 1 → Y.stk 2 = pushAcc inY pre ++ s.stk 2 →
      (∀ j : Stk, j ≠ 0 → j ≠ 1 → j ≠ 2 → Y.stk j = s.stk j) →
      ∃ (Y' : State) (n : ℕ), n ≤ gs.length * (b + 3) + 5 ∧
        Eval main (splitLoop r) Y Y' n ∧ Y'.stk 0 = [] ∧
        Y'.stk 1 = pushAcc inX (gs.reverse ++ pre) ++ s.stk 1 ∧
        Y'.stk 2 = pushAcc inY (gs.reverse ++ pre) ++ s.stk 2 ∧ Y'.reg r = Glyph.mk 15 ∧
        (∀ j : Stk, j ≠ 0 → j ≠ 1 → j ≠ 2 → Y'.stk j = s.stk j) := by
  intro gs
  induction gs with
  | nil =>
    -- stack 0 is already empty: the loop pops `eos`, sets the test register to `mk 15` and stops
    intro pre s Y hne h0 hreg h1 h2 hoth
    refine ⟨State.tSet (State.tPop Y 0 r) r (Glyph.mk 15), 5, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · have hY1reg : (State.tPop Y 0 r).reg r = Glyph.eos := by simp [State.tPop, h0]
      have hbody := eval_splitBody_exit main r Y hY1reg
      have hloopF : Eval main (splitLoop r) (State.tSet (State.tPop Y 0 r) r (Glyph.mk 15))
          (State.tSet (State.tPop Y 0 r) r (Glyph.mk 15)) 1 := by
        apply eval_loopF
        simp [State.tSet, State.updReg]
      simpa [splitLoop] using Eval.loopT hreg hbody hloopF
    · simp [State.tSet, State.tPop, h0]
    · simp [State.tSet, State.tPop, h1]
    · simp [State.tSet, State.tPop, h2]
    · simp [State.tSet, State.updReg]
    · intro j hj0 hj1 hj2
      simp [State.tSet, State.tPop, hj0, hoth j hj0 hj1 hj2]
  | cons g gs' ih =>
    intro pre s Y hne h0 hreg h1 h2 hoth
    have hgne : g ≠ Glyph.eos := hne g (by simp)
    have hne' : ∀ g' ∈ gs', g' ≠ Glyph.eos := fun g' hg' => hne g' (by simp [hg'])
    -- the first iteration: pop `g`, then dispatch with `splitCmd` and reset the test register
    have hY1reg : (State.tPop Y 0 r).reg r = g := by simp [State.tPop, h0]
    have hY1s0 : (State.tPop Y 0 r).stk 0 = gs' := by simp [State.tPop, h0]
    have hY1s1 : (State.tPop Y 0 r).stk 1 = Y.stk 1 := by simp [State.tPop]
    have hY1s2 : (State.tPop Y 0 r).stk 2 = Y.stk 2 := by simp [State.tPop]
    have hY1oth : ∀ j : Stk, j ≠ 0 → (State.tPop Y 0 r).stk j = Y.stk j := by
      intro j hj; simp [State.tPop, hj]
    obtain ⟨Y2, n2, hn2, hev2, hY2s0, hY2s1, hY2s2, hY2reg, hY2oth⟩ :=
      hbranch g (State.tPop Y 0 r) hgne hY1reg
    have hstep : Eval main (splitBody r) Y Y2 (n2 + 2) :=
      eval_splitBody_step main r Y (by rw [hY1reg]; exact hgne) hev2
    -- the invariant is maintained, with `pre` replaced by `g :: pre`
    have hY2s0' : Y2.stk 0 = gs' := by rw [hY2s0, hY1s0]
    have hY2s1' : Y2.stk 1 = pushAcc inX (g :: pre) ++ s.stk 1 := by
      rw [hY2s1, hY1s1, h1, pushAcc_cons]; simp [List.append_assoc]
    have hY2s2' : Y2.stk 2 = pushAcc inY (g :: pre) ++ s.stk 2 := by
      rw [hY2s2, hY1s2, h2, pushAcc_cons]; simp [List.append_assoc]
    have hY2oth' : ∀ j : Stk, j ≠ 0 → j ≠ 1 → j ≠ 2 → Y2.stk j = s.stk j := by
      intro j hj0 hj1 hj2
      rw [hY2oth j hj0 hj1 hj2, hY1oth j hj0, hoth j hj0 hj1 hj2]
    obtain ⟨Y3, n3, hn3, hev3, hY3s0, hY3s1, hY3s2, hY3reg, hY3oth⟩ :=
      ih (g :: pre) s Y2 hne' hY2s0' hY2reg hY2s1' hY2s2' hY2oth'
    refine ⟨Y3, n2 + 2 + n3 + 1, ?_, ?_, hY3s0, ?_, ?_, hY3reg, hY3oth⟩
    · -- cost: `n2 + 2` for the iteration, `n3` for the rest, `1` for the loop test
      have hlen : (g :: gs').length = gs'.length + 1 := List.length_cons ..
      have h3 : (gs'.length + 1) * (b + 3) = gs'.length * (b + 3) + (b + 3) := by ring
      rw [hlen, h3]
      omega
    · simpa [splitLoop] using Eval.loopT hreg hstep hev3
    · rw [hY3s1]
      have hrev : (g :: gs').reverse ++ pre = gs'.reverse ++ (g :: pre) := by
        simp [List.reverse_cons, List.append_assoc]
      rw [hrev]
    · rw [hY3s2]
      have hrev : (g :: gs').reverse ++ pre = gs'.reverse ++ (g :: pre) := by
        simp [List.reverse_cons, List.append_assoc]
      rw [hrev]

theorem splitLoopEval (main : HvdH.Cmd) (r : HvdH.Reg) (b : ℕ)
    (hbranch : ∀ (g : HvdH.Glyph) (Y : HvdH.State), g ≠ HvdH.Glyph.eos → Y.reg r = g →
      ∃ (Y' : HvdH.State) (n : ℕ), n ≤ b ∧
        HvdH.Eval main (HvdH.Cmd.seq (Work.IntLib.splitCmd r) (HvdH.Cmd.set r HvdH.Glyph.eos)) Y Y' n ∧
        Y'.stk 0 = Y.stk 0 ∧ Y'.stk 1 = Work.IntLib.inX g ++ Y.stk 1 ∧
        Y'.stk 2 = Work.IntLib.inY g ++ Y.stk 2 ∧ Y'.reg r = HvdH.Glyph.eos ∧
        (∀ j : HvdH.Stk, j ≠ 0 → j ≠ 1 → j ≠ 2 → Y'.stk j = Y.stk j)) :
    ∀ (gs pre : List HvdH.Glyph) (s X : HvdH.State), (∀ g ∈ gs, g ≠ HvdH.Glyph.eos) →
      X.stk 0 = gs → X.reg r = HvdH.Glyph.eos →
      X.stk 1 = Work.IntLib.pushAcc Work.IntLib.inX pre ++ s.stk 1 →
      X.stk 2 = Work.IntLib.pushAcc Work.IntLib.inY pre ++ s.stk 2 →
      (∀ j : HvdH.Stk, j ≠ 0 → j ≠ 1 → j ≠ 2 → X.stk j = s.stk j) →
      ∃ (X' : HvdH.State) (n : ℕ), n ≤ (gs.length + 1) * (b + 4) + 1 ∧
        HvdH.Eval main (Work.IntLib.splitLoop r) X X' n ∧ X'.stk 0 = [] ∧
        X'.stk 1 = Work.IntLib.pushAcc Work.IntLib.inX (gs.reverse ++ pre) ++ s.stk 1 ∧
        X'.stk 2 = Work.IntLib.pushAcc Work.IntLib.inY (gs.reverse ++ pre) ++ s.stk 2 ∧
        X'.reg r ≠ HvdH.Glyph.eos ∧
        (∀ j : HvdH.Stk, j ≠ 0 → j ≠ 1 → j ≠ 2 → X'.stk j = s.stk j) := by
  intro gs pre s X hne h0 hreg h1 h2 hoth
  obtain ⟨X', n, hn, hev, hX0, hX1, hX2, hXreg, hXoth⟩ :=
    splitLoop_aux main r b hbranch gs pre s X hne h0 hreg h1 h2 hoth
  refine ⟨X', n, ?_, hev, hX0, hX1, hX2, ?_, hXoth⟩
  · have h3 : (gs.length + 1) * (b + 4) = gs.length * (b + 4) + (b + 4) := by ring
    have h4 : gs.length * (b + 3) ≤ gs.length * (b + 4) := Nat.mul_le_mul_left _ (by omega)
    rw [h3]
    omega
  · rw [hXreg]; decide

end Work.IntLib
