import Mathlib
import Submission.Work.ConvR.flagDefs
import Submission.Work.ConvR.flagAux
import Submission.Work.ConvR.eval_readBody_cont

/-!
# ConvR: correctness and cost of the read loop `readLoop`

`readLoop rs rd rf rv` moves the glyphs of the encoded value `l₁ ++ [iend]` from the stack `rs` to
the stack `rd` (reversed, so that the top of `rd` afterwards is the last glyph read, i.e. `iend`),
leaving `rv = iend` and the loop flag `rf` at `mk 2`, and stopping just after the `iend` is read.

This file proves the exact `Eval` statement together with the cost `5 * (l₁.length + 1) + 2`:
each of the `l₁.length + 1` iterations costs `pop` (1) + `push` (1) + the `ite` test (1) + the branch
(1: `skip`, resp. `set rf (mk 2)`) = 4, the loop tests cost one more each, and the preliminary
`set rf (mk 1)` costs 1.

The proof is by induction on `l₁`; the auxiliary lemmas record (i) the last (`iend`) iteration, (ii)
one continuing iteration at the level of final states, and (iii) that writing the loop flag before
entering the loop is erased by the final state (`readFin` never looks at `rf`, and `rv ≠ rf`).
-/

set_option autoImplicit false

namespace Work.ConvR

open HvdH

section Aux

/-- The final (`iend`) iteration of the read loop: reading the terminating `iend` (and pushing it on
`rd`) and stopping agrees with `readFin` when there is nothing left to read. -/
theorem readFin_nil (rs rd : Stk) (rf rv : Reg) (l₂ : List Glyph) (t : State)
    (hrd : rd ≠ rs) (h : t.stk rs = Glyph.iend :: l₂) :
    (State.tPush (State.tPop t rs rv) rd rv).updReg rf (Glyph.mk 2)
      = (readFin rs rd rv [] l₂ t).updReg rf (Glyph.mk 2) := by
  apply FlagAux.State.ext_stk_reg
  · intro k
    by_cases hk : k = rd <;> by_cases hk2 : k = rs <;>
      simp_all [readFin, State.tPop, State.tPush, List.reverse_cons, List.append_assoc]
  · intro r
    by_cases hr : r = rv <;> simp_all [readFin, State.tPop, State.tPush]

/-- One continuing iteration of the body of `readLoop`, seen at the level of final states: moving
the glyph `g` (the head of the remaining part of `rs`, not `iend`) over to `rd` turns the final state
for `l₁'` into the final state for `g :: l₁'`. -/
theorem readFin_step (rs rd : Stk) (rv : Reg) (g : Glyph) (l₁' l₂ : List Glyph) (t : State)
    (hrd : rd ≠ rs) (h : t.stk rs = g :: (l₁' ++ Glyph.iend :: l₂)) :
    readFin rs rd rv l₁' l₂ (State.tPush (State.tPop t rs rv) rd rv)
      = readFin rs rd rv (g :: l₁') l₂ t := by
  apply FlagAux.State.ext_stk_reg
  · intro k
    by_cases hk : k = rd <;> by_cases hk2 : k = rs <;>
      simp_all [readFin, State.tPop, State.tPush, List.reverse_cons, List.append_assoc]
  · intro r
    by_cases hr : r = rv <;> simp_all [readFin, State.tPop, State.tPush]

/-- The preliminary `set rf (mk 1)` is invisible in the final state, because `readFin` never looks at
the loop flag (here `rv ≠ rf`, so writing `rv` cannot clobber `rf` either). -/
theorem readFin_updReg_rf (rs rd : Stk) (rf rv : Reg) (g : Glyph) (l₁ l₂ : List Glyph)
    (t : State) (hrv : rv ≠ rf) :
    readFin rs rd rv l₁ l₂ (t.updReg rf g) = (readFin rs rd rv l₁ l₂ t).updReg rf g := by
  apply FlagAux.State.ext_stk_reg
  · intro k
    by_cases hk : k = rd <;> by_cases hk2 : k = rs <;> simp_all [readFin]
  · intro r
    by_cases hr : r = rf <;> by_cases hr2 : r = rv <;> simp_all [readFin]

/-- One pass of the read-loop body when the popped glyph *is* `iend`: the glyph is moved to `rd` and
the loop flag is set to `mk 2` (so the loop stops).  Cost: `pop` 1 + `push` 1 + `ite`
(test + `set`) 2 = 4. -/
theorem eval_readBody_iend (main : Cmd) (rs rd : Stk) (rf rv : Reg) (l₂ : List Glyph) (s : State)
    (hs : s.stk rs = Glyph.iend :: l₂) :
    Eval main (readBody rs rd rf rv) s
      ((State.tPush (State.tPop s rs rv) rd rv).updReg rf (Glyph.mk 2)) 4 := by
  unfold readBody
  have h1 : Eval main (Cmd.pop rs rv) s (State.tPop s rs rv) 1 := Eval.pop rs rv s
  have h2 : Eval main (Cmd.push rd rv) (State.tPop s rs rv)
      (State.tPush (State.tPop s rs rv) rd rv) 1 := Eval.push rd rv _
  have h3 : (State.tPop s rs rv).reg rv = Glyph.iend := by
    rw [State.tPop]
    simp only [State.updReg_apply, ite_true, State.updStk_reg]
    rw [hs]
    rfl
  have hI : Eval main (Cmd.ite rv Glyph.iend (Cmd.set rf (Glyph.mk 2)) Cmd.skip)
      (State.tPush (State.tPop s rs rv) rd rv)
      ((State.tPush (State.tPop s rs rv) rd rv).updReg rf (Glyph.mk 2)) 2 :=
    Eval.iteT h3 (Eval.set rf (Glyph.mk 2) _)
  exact Eval.seq h1 (Eval.seq h2 hI)

/-- The loop of `readLoop`, from a state whose loop flag is already `mk 1`: cost
`5 * (l₁.length + 1) + 1` (the loop tests one more time than the body runs). -/
theorem eval_readLoop_loop (main : Cmd) (rs rd : Stk) (rf rv : Reg) (hrd : rd ≠ rs)
    (hrv : rv ≠ rf) :
    ∀ (l₁ l₂ : List Glyph) (s : State), Glyph.iend ∉ l₁ → s.reg rf = Glyph.mk 1 →
      s.stk rs = l₁ ++ Glyph.iend :: l₂ →
      Eval main (Cmd.loop rf (Glyph.mk 1) (readBody rs rd rf rv)) s
        ((readFin rs rd rv l₁ l₂ s).updReg rf (Glyph.mk 2)) (5 * (l₁.length + 1) + 1) := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ s hno hrf hstk
    have hbody := eval_readBody_iend main rs rd rf rv l₂ s hstk
    have hstop : ((State.tPush (State.tPop s rs rv) rd rv).updReg rf (Glyph.mk 2)).reg rf
        ≠ Glyph.mk 1 := by simp
    have hend : Eval main (Cmd.loop rf (Glyph.mk 1) (readBody rs rd rf rv))
        ((State.tPush (State.tPop s rs rv) rd rv).updReg rf (Glyph.mk 2))
        ((State.tPush (State.tPop s rs rv) rd rv).updReg rf (Glyph.mk 2)) 1 :=
      Eval.loopF hstop
    have hT := Eval.loopT (r := rf) (c := Glyph.mk 1) hrf hbody hend
    rw [readFin_nil rs rd rf rv l₂ s hrd hstk] at hT
    have hc : 4 + 1 + 1 = 5 * (([] : List Glyph).length + 1) + 1 := by simp
    exact hc ▸ hT
  | cons g l₁' ih =>
    intro l₂ s hno hrf hstk
    have hg : g ≠ Glyph.iend := fun hh => hno (by rw [hh]; exact List.mem_cons_self ..)
    have hno' : Glyph.iend ∉ l₁' := fun hh => hno (List.mem_cons_of_mem g hh)
    have hbody := eval_readBody_cont main rs rd rf rv g hg (l₁' ++ Glyph.iend :: l₂) s hstk
    have hstk' : (State.tPush (State.tPop s rs rv) rd rv).stk rs
        = l₁' ++ Glyph.iend :: l₂ := by
      simp [State.tPush, State.tPop, hstk, Ne.symm hrd]
    have hrf' : (State.tPush (State.tPop s rs rv) rd rv).reg rf = Glyph.mk 1 := by
      simp [State.tPush, State.tPop, hrf, Ne.symm hrv]
    have hrest := ih l₂ (State.tPush (State.tPop s rs rv) rd rv) hno' hrf' hstk'
    have hT := Eval.loopT (r := rf) (c := Glyph.mk 1) hrf hbody hrest
    rw [readFin_step rs rd rv g l₁' l₂ s hrd hstk] at hT
    have hc : 4 + (5 * (l₁'.length + 1) + 1) + 1 = 5 * ((g :: l₁').length + 1) + 1 := by
      simp [List.length_cons]; ring
    exact hc ▸ hT

end Aux

/-- `readLoop rs rd rf rv` reads the encoded value `l₁ ++ [iend]` from the stack `rs`, moving its
glyphs (reversed) to the stack `rd` and stopping just after the `iend` has been read. -/
theorem eval_readLoop (main : Cmd) (rs rd : Stk) (rf rv : Reg) (hrd : rd ≠ rs) (hrv : rv ≠ rf) :
    ∀ (l₁ l₂ : List Glyph), Glyph.iend ∉ l₁ → ∀ s : State,
      s.stk rs = l₁ ++ Glyph.iend :: l₂ →
      Eval main (readLoop rs rd rf rv) s
        ((readFin rs rd rv l₁ l₂ s).updReg rf (Glyph.mk 2))
        (5 * (l₁.length + 1) + 2) := by
  intro l₁ l₂ hno s hstk
  unfold readLoop
  have hset : Eval main (Cmd.set rf (Glyph.mk 1)) s (s.updReg rf (Glyph.mk 1)) 1 :=
    Eval.set rf (Glyph.mk 1) s
  have hloop := eval_readLoop_loop main rs rd rf rv hrd hrv l₁ l₂ (s.updReg rf (Glyph.mk 1))
    hno (by simp) (by simpa using hstk)
  have hcomb := Eval.seq hset hloop
  rw [readFin_updReg_rf (rs := rs) (rd := rd) (rf := rf) (rv := rv) (g := Glyph.mk 1)
      (l₁ := l₁) (l₂ := l₂) (t := s) hrv, State.updReg_updReg] at hcomb
  have hcost : 1 + (5 * (l₁.length + 1) + 1) = 5 * (l₁.length + 1) + 2 := by ring
  exact hcost ▸ hcomb

end Work.ConvR
