import Mathlib
import Submission.Work.IntLib.UR.Defs
import Submission.Work.Kernel.Raw
import Submission.Work.Layout.Base

/-!
# IntLib: `urPhase2Loop` — moving the tokens back, doubling them

`urPhase2Loop c tr` is the second half of the doubling step of `unaryRebuild`: it moves the `v`
tokens of the unary counter `Unary v Tr` from the scratch stack `tr` back onto the stack `c`,
writing **two** tokens for each one moved, so that the counter on `c` becomes `Unary (j + 2v) Gc`
(if it started as `Unary j Gc`).

The body `urPhase2Body c tr` pops one token from `tr` into `rD`, pushes `gTok` twice on `c`, and
finally peeks the new head of `tr` into `rD`; the loop test `rD = gTok` therefore succeeds exactly
as long as a token is left on `tr`, and fails after `v` iterations (when the head becomes `gEnd`).
Total cost `5v + 1` (four steps per iteration plus the loop test, plus one final test).

This file proves the `Eval` statement for every `main`; it is one of the two lemma-level pieces of
`Work.IntLib.unaryRebuild`.
-/

set_option autoImplicit false

namespace Work.IntLib.UR

open HvdH

/-! ## Auxiliary facts -/

theorem urPhase2_two_toks (j : ℕ) (Gc : List Glyph) :
    gTok :: gTok :: Unary j Gc = Unary (j + 2) Gc := by
  rw [show j + 2 = j + 1 + 1 from by omega, Unary_succ, Unary_succ]

/-! ## One iteration of the body

`urPhase2Body c tr` is `pop tr rD ; push c rTok ; push c rTok ; peek tr rD`.  One iteration
therefore moves one glyph from `tr` to `c` twice over. -/

/-- The state reached after running one iteration of `urPhase2Body c tr` from `s`. -/
def ph2Step (c tr : Stk) (s : State) : State :=
  State.tPeek (State.tPush (State.tPush (State.tPop s tr rD) c rTok) c rTok) tr rD

/-- The body runs in exactly four steps. -/
theorem ev_ph2Step (main : Cmd) (c tr : Stk) (s : State) :
    Work.Layout.Ev main (urPhase2Body c tr) s (ph2Step c tr s) 4 := by
  have e1 : Eval main (.pop tr rD) s (State.tPop s tr rD) 1 := Work.Kernel.eval_pop main tr rD s
  have e2 : Eval main (.push c rTok) (State.tPop s tr rD)
      (State.tPush (State.tPop s tr rD) c rTok) 1 :=
    Work.Kernel.eval_push main c rTok (State.tPop s tr rD)
  have e3 : Eval main (.push c rTok) (State.tPush (State.tPop s tr rD) c rTok)
      (State.tPush (State.tPush (State.tPop s tr rD) c rTok) c rTok) 1 :=
    Work.Kernel.eval_push main c rTok (State.tPush (State.tPop s tr rD) c rTok)
  have e4 : Eval main (.peek tr rD) (State.tPush (State.tPush (State.tPop s tr rD) c rTok) c rTok)
      (ph2Step c tr s) 1 :=
    Work.Kernel.eval_peek main tr rD (State.tPush (State.tPush (State.tPop s tr rD) c rTok) c rTok)
  unfold urPhase2Body
  exact ⟨4, Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4)), by omega⟩

/-! ## Components of the resulting state

All five are proved by unfolding `ph2Step` and normalising the `Function.update`s. -/

/-- One token has left `tr`. -/
theorem ph2Step_stk_tr {c tr : Stk} (hct : c ≠ tr) (s : State) :
    (ph2Step c tr s).stk tr = (s.stk tr).tail := by
  simp [ph2Step, State.tPeek, State.tPush, State.tPop, State.updStk, State.updReg, hct, hct.symm]

/-- Two tokens have arrived on `c`. -/
theorem ph2Step_stk_c {c tr : Stk} (hct : c ≠ tr) (s : State) :
    (ph2Step c tr s).stk c = s.reg rTok :: s.reg rTok :: s.stk c := by
  simp [ph2Step, State.tPeek, State.tPush, State.tPop, State.updStk, State.updReg, hct, hct.symm,
    rTok_ne_rD]

/-- The token register is left alone. -/
theorem ph2Step_reg_rTok {c tr : Stk} (s : State) :
    (ph2Step c tr s).reg rTok = s.reg rTok := by
  simp [ph2Step, State.tPeek, State.tPush, State.tPop, State.updStk, State.updReg, rTok_ne_rD]

/-- The loop register now holds the new head of `tr`. -/
theorem ph2Step_reg_rD {c tr : Stk} (hct : c ≠ tr) (s : State) :
    (ph2Step c tr s).reg rD = (s.stk tr).tail.headD Glyph.eos := by
  simp [ph2Step, State.tPeek, State.tPush, State.tPop, State.updStk, State.updReg, hct.symm]

/-- Every other stack is untouched. -/
theorem ph2Step_stk_of_ne {c tr k : Stk} (hct : c ≠ tr) (hk1 : k ≠ c) (hk2 : k ≠ tr) (s : State) :
    (ph2Step c tr s).stk k = s.stk k := by
  simp [ph2Step, State.tPeek, State.tPush, State.tPop, State.updStk, State.updReg, hct, hct.symm,
    hk1, hk2]

/-! ## The loop

Starting from any state whose stack `tr` holds a unary counter of value `u`, whose stack `c` holds
the counter to grow, and whose loop register `rD` holds the head of the counter on `tr`: after `u`
iterations `tr` is empty and `c` has grown by `2u`. -/

theorem phase2_loopRuns (main : Cmd) (c tr : Stk) (hct : c ≠ tr) :
    ∀ (u j : ℕ) (Tr Gc : List Glyph) (s : State),
      s.stk tr = Unary u Tr → s.stk c = Unary j Gc → s.reg rTok = gTok →
      s.reg rD = (Unary u Tr).headD Glyph.eos →
      ∃ s', Work.Layout.loopRuns main rD gTok (urPhase2Body c tr) u s s' (5 * u) ∧
        s'.stk tr = Unary 0 Tr ∧ s'.stk c = Unary (j + 2 * u) Gc ∧
        s'.reg rD = (Unary 0 Tr).headD Glyph.eos ∧
        (∀ k : Stk, k ≠ c → k ≠ tr → s'.stk k = s.stk k) := by
  intro u
  induction u with
  | zero =>
      intro j Tr Gc s htr hc htok hr
      exact ⟨s, Work.Layout.loopRuns.zero, htr, by simpa using hc, hr, fun k _ _ => rfl⟩
  | succ u ih =>
      intro j Tr Gc s htr hc htok hr
      have hT : (s.stk tr).tail = Unary u Tr := by simp [htr, Unary_succ]
      obtain ⟨s₂, hrun, h1, h2, h3, h4⟩ :=
        ih (j + 2) Tr Gc (ph2Step c tr s)
          (by rw [ph2Step_stk_tr hct, hT])
          (by rw [ph2Step_stk_c hct, htok, hc]; exact urPhase2_two_toks j Gc)
          (by rw [ph2Step_reg_rTok, htok])
          (by rw [ph2Step_reg_rD hct, hT])
      have htest : s.reg rD = gTok := by
        rw [hr]
        exact Unary_headD_ne Tr Glyph.eos (by omega)
      refine ⟨s₂, Work.Layout.loopRuns.succ' htest (ev_ph2Step main c tr s) hrun (by omega), h1, ?_, h3, ?_⟩
      · rw [h2]; congr 1; omega
      · intro k hk1 hk2
        rw [h4 k hk1 hk2, ph2Step_stk_of_ne hct hk1 hk2]

/-! ## The `phase2_eval` statement -/

theorem phase2_eval (main : HvdH.Cmd) (c tr : HvdH.Stk) (hct : c ≠ tr) (v j : ℕ)
    (Gc Tr : List HvdH.Glyph) (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph)
    (htr : X tr = Work.IntLib.Unary v Tr) (hc : X c = Work.IntLib.Unary j Gc)
    (hr : g Work.IntLib.UR.rD = (Work.IntLib.Unary v Tr).headD HvdH.Glyph.eos)
    (hrTok : g Work.IntLib.UR.rTok = Work.IntLib.gTok) :
    ∃ (g' : HvdH.Reg → HvdH.Glyph) (X' : HvdH.Stk → List HvdH.Glyph) (n : ℕ),
      Work.Layout.Ev main (Work.IntLib.UR.urPhase2Loop c tr) ⟨g, X⟩ ⟨g', X'⟩ n ∧ n ≤ 5 * v + 2 ∧
      X' tr = Work.IntLib.Unary 0 Tr ∧ X' c = Work.IntLib.Unary (j + 2 * v) Gc ∧
      (∀ k : HvdH.Stk, k ≠ c → k ≠ tr → X' k = X k) := by
  obtain ⟨s', hrun, h1, h2, h3, h4⟩ :=
    phase2_loopRuns main c tr hct v j Tr Gc ⟨g, X⟩ htr hc hrTok hr
  have hne : s'.reg rD ≠ gTok := by
    rw [h3, Unary_headD_zero]
    exact Work.IntLib.gEnd_ne_gTok
  obtain ⟨n, hev, hn⟩ := Work.Layout.loopRuns.eval hrun hne
  exact ⟨s'.reg, s'.stk, n, ⟨n, hev, le_rfl⟩, by omega, h1, h2, h4⟩

end Work.IntLib.UR
