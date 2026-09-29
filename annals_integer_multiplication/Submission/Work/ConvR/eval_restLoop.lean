import Mathlib
import Submission.Work.ConvR.flagDefs

namespace Work.ConvR

open HvdH

/-!
# ConvR: correctness and cost of the restore loop `restLoop`

`restLoop rs rd rf rv m` moves the glyphs lying above the frame marker `m` on the stack `rs` to the
stack `rd` (reversed, so that the top of `rd` afterwards is what was the deepest glyph moved), drops
the marker `m`, and leaves it in register `rv`; the loop flag `rf` ends at `mk 2`.

This file proves the exact `Eval` statement (`eval_restLoop`) together with the cost
`4 * (B.length + 1) + 2`, where `B` is the list of glyphs above the marker.  The two loop iterations
per moved glyph (plus one for the marker) come from `pop` (1) + the `ite` test (1) + the `push` (1)
plus the loop test (1).

The proof is by induction on `B`; the auxiliary lemmas below record (i) how the body transforms the
state (`restFin_step`), (ii) the final (marker) iteration (`restFin_nil`) and (iii) that setting the
loop flag `rf` before entering the loop is erased by the final `restFin` (`restFin_updReg_rf`, where
the hypothesis `rv ≠ rf` is used).
-/

section Aux

/-- One iteration of the body of `restLoop`, seen at the level of final states: moving the glyph `b`
(the head of the remaining part of `rs`, above the marker) over to `rd` turns the final state for
`B'` into the final state for `b :: B'`. -/
theorem restFin_step (rs rd : Stk) (rv : Reg) (m b : Glyph) (B' l₀ : List Glyph) (t : State)
    (hrd : rd ≠ rs) (h : t.stk rs = b :: (B' ++ m :: l₀)) :
    restFin rs rd rv m B' l₀ (State.tPush (State.tPop t rs rv) rd rv)
      = restFin rs rd rv m (b :: B') l₀ t := by
  apply FlagAux.State.ext_stk_reg
  · intro k
    by_cases hk : k = rd <;> by_cases hk2 : k = rs <;>
      simp_all [restFin, State.tPop, State.tPush, List.reverse_cons, List.append_assoc]
  · intro r
    by_cases hr : r = rv <;> simp_all [restFin, State.tPop, State.tPush]

/-- The final (marker) iteration of the loop: reading the marker `m` and stopping agrees with
`restFin` when there is nothing left to move. -/
theorem restFin_nil (rs rd : Stk) (rf rv : Reg) (m : Glyph) (l₀ : List Glyph) (t : State)
    (hrd : rd ≠ rs) (h : t.stk rs = m :: l₀) :
    (State.tPop t rs rv).updReg rf (Glyph.mk 2)
      = (restFin rs rd rv m [] l₀ t).updReg rf (Glyph.mk 2) := by
  apply FlagAux.State.ext_stk_reg
  · intro k
    by_cases hk : k = rd <;> by_cases hk2 : k = rs <;> simp_all [restFin, State.tPop]
  · intro r
    by_cases hr : r = rf <;> by_cases hr2 : r = rv <;> simp_all [restFin, State.tPop]

/-- The preliminary `set rf (mk 1)` is invisible in the final state, because `restFin` never looks at
the loop flag (here `rv ≠ rf`, so writing `rv` cannot clobber `rf` either). -/
theorem restFin_updReg_rf (rs rd : Stk) (rf rv : Reg) (m g : Glyph) (B l₀ : List Glyph)
    (t : State) (hrv : rv ≠ rf) :
    restFin rs rd rv m B l₀ (t.updReg rf g) = (restFin rs rd rv m B l₀ t).updReg rf g := by
  apply FlagAux.State.ext_stk_reg
  · intro k
    by_cases hk : k = rd <;> by_cases hk2 : k = rs <;> simp_all [restFin]
  · intro r
    by_cases hr : r = rf <;> by_cases hr2 : r = rv <;> simp_all [restFin]

/-- One iteration of the body of `restLoop` when the head of `rs` is not the marker: the glyph is
popped (cost 1) and pushed on `rd` (cost 1) through the `ite` test (cost 1). -/
theorem eval_restBody_cons (main : Cmd) (rs rd : Stk) (rf rv : Reg) (m b : Glyph)
    (B' l₀ : List Glyph) (hm : m ∉ b :: B') (t : State) (h : t.stk rs = b :: (B' ++ m :: l₀)) :
    Eval main (restBody rs rd rf rv m) t (State.tPush (State.tPop t rs rv) rd rv) 3 := by
  unfold restBody
  have hb : b ≠ m := fun hh => hm (by simp [hh])
  have hhead : (t.stk rs).head?.getD Glyph.eos = b := by rw [h]; rfl
  have h1 : Eval main (Cmd.pop rs rv) t (State.tPop t rs rv) 1 := Eval.pop rs rv t
  have hreg : (State.tPop t rs rv).reg rv = b := by simp [State.tPop, hhead]
  have h2 : Eval main (Cmd.ite rv m (Cmd.set rf (Glyph.mk 2)) (Cmd.push rd rv))
      (State.tPop t rs rv) (State.tPush (State.tPop t rs rv) rd rv) 2 :=
    Eval.iteF (by rw [hreg]; exact hb) (Eval.push rd rv (State.tPop t rs rv))
  exact Eval.seq h1 h2

/-- The last iteration of the body of `restLoop`: the marker is popped and the loop flag is set to
`mk 2` (cost 1 each for the `pop`, the `ite` test and the `set`). -/
theorem eval_restBody_nil (main : Cmd) (rs rd : Stk) (rf rv : Reg) (m : Glyph)
    (l₀ : List Glyph) (t : State) (h : t.stk rs = m :: l₀) :
    Eval main (restBody rs rd rf rv m) t ((State.tPop t rs rv).updReg rf (Glyph.mk 2)) 3 := by
  unfold restBody
  have hhead : (t.stk rs).head?.getD Glyph.eos = m := by rw [h]; rfl
  have h1 : Eval main (Cmd.pop rs rv) t (State.tPop t rs rv) 1 := Eval.pop rs rv t
  have hreg : (State.tPop t rs rv).reg rv = m := by simp [State.tPop, hhead]
  have h2 : Eval main (Cmd.ite rv m (Cmd.set rf (Glyph.mk 2)) (Cmd.push rd rv))
      (State.tPop t rs rv) ((State.tPop t rs rv).updReg rf (Glyph.mk 2)) 2 :=
    Eval.iteT hreg (Eval.set rf (Glyph.mk 2) (State.tPop t rs rv))
  exact Eval.seq h1 h2

/-- The bare loop `loop rf (mk 1) (restBody …)`, entered with the flag already set: it moves the
glyphs of `B` from `rs` to `rd` and stops on the marker `m`, at cost `4 * (B.length + 1) + 1`. -/
theorem eval_restLoop_loop (main : Cmd) (rs rd : Stk) (rf rv : Reg) (m : Glyph) (hrd : rd ≠ rs)
    (hrv : rv ≠ rf) :
    ∀ (B l₀ : List Glyph), m ∉ B → ∀ t : State, t.reg rf = Glyph.mk 1 → t.stk rs = B ++ m :: l₀ →
      Eval main (Cmd.loop rf (Glyph.mk 1) (restBody rs rd rf rv m)) t
        ((restFin rs rd rv m B l₀ t).updReg rf (Glyph.mk 2)) (4 * (B.length + 1) + 1) := by
  intro B
  induction B with
  | nil =>
    intro l₀ hm t hrf h
    have hbody := eval_restBody_nil main rs rd rf rv m l₀ t h
    have hstop : ((State.tPop t rs rv).updReg rf (Glyph.mk 2)).reg rf ≠ Glyph.mk 1 := by simp
    have hend : Eval main (Cmd.loop rf (Glyph.mk 1) (restBody rs rd rf rv m))
        ((State.tPop t rs rv).updReg rf (Glyph.mk 2))
        ((State.tPop t rs rv).updReg rf (Glyph.mk 2)) 1 :=
      Eval.loopF hstop
    have hT := Eval.loopT (r := rf) (c := Glyph.mk 1) hrf hbody hend
    have hst : ((State.tPop t rs rv).updReg rf (Glyph.mk 2))
        = (restFin rs rd rv m [] l₀ t).updReg rf (Glyph.mk 2) :=
      restFin_nil rs rd rf rv m l₀ t hrd h
    rw [hst] at hT
    exact hT
  | cons b B' ih =>
    intro l₀ hm t hrf h
    have hm' : m ∉ B' := fun hh => hm (List.mem_cons_of_mem b hh)
    have hbody := eval_restBody_cons main rs rd rf rv m b B' l₀ hm t h
    have hrf' : (State.tPush (State.tPop t rs rv) rd rv).reg rf = Glyph.mk 1 := by
      simpa [State.tPush, State.tPop, State.updReg_apply, Ne.symm hrv] using hrf
    have hrs' : (State.tPush (State.tPop t rs rv) rd rv).stk rs = B' ++ m :: l₀ := by
      simp [State.tPush, State.tPop, h, hrd, Ne.symm hrd]
    have hrest := ih l₀ hm' (State.tPush (State.tPop t rs rv) rd rv) hrf' hrs'
    have hT := Eval.loopT (r := rf) (c := Glyph.mk 1) hrf hbody hrest
    have hstate : (restFin rs rd rv m B' l₀
          (State.tPush (State.tPop t rs rv) rd rv)).updReg rf (Glyph.mk 2)
        = (restFin rs rd rv m (b :: B') l₀ t).updReg rf (Glyph.mk 2) := by
      rw [restFin_step rs rd rv m b B' l₀ t hrd h]
    rw [hstate] at hT
    have hcost : 3 + (4 * (B'.length + 1) + 1) + 1 = 4 * ((b :: B').length + 1) + 1 := by
      simp [List.length_cons]; ring
    exact hcost ▸ hT

end Aux

namespace Work.ConvR

open HvdH

/-- `restLoop rs rd rf rv m` moves the glyphs `B` lying above the frame marker `m` on the stack
`rs` to the stack `rd` (reversed), dropping the marker `m` itself. -/
theorem eval_restLoop (main : Cmd) (rs rd : Stk) (rf rv : Reg) (m : Glyph) (hrd : rd ≠ rs)
    (hrv : rv ≠ rf) :
    ∀ (B l₀ : List Glyph), m ∉ B → ∀ s : State,
      s.stk rs = B ++ m :: l₀ →
      Eval main (restLoop rs rd rf rv m) s
        ((restFin rs rd rv m B l₀ s).updReg rf (Glyph.mk 2))
        (4 * (B.length + 1) + 2) := by
  intro B l₀ hm s hs
  unfold restLoop
  have hset : Eval main (Cmd.set rf (Glyph.mk 1)) s (s.updReg rf (Glyph.mk 1)) 1 :=
    Eval.set rf (Glyph.mk 1) s
  have hloop := eval_restLoop_loop main rs rd rf rv m hrd hrv B l₀ hm (s.updReg rf (Glyph.mk 1))
    (by simp) (by simpa using hs)
  have hcomb := Eval.seq hset hloop
  rw [restFin_updReg_rf (rs := rs) (rd := rd) (rf := rf) (rv := rv) (m := m)
      (g := Glyph.mk 1) (B := B) (l₀ := l₀) (t := s) hrv, State.updReg_updReg] at hcomb
  have hcost : 1 + (4 * (B.length + 1) + 1) = 4 * (B.length + 1) + 2 := by ring
  exact hcost ▸ hcomb

end Work.ConvR

/-- Same statement as `Work.ConvR.Work.ConvR.eval_restLoop`, under the plain name
`Work.ConvR.eval_restLoop` (the statement as requested was wrapped in its own `namespace
Work.ConvR`). -/
theorem eval_restLoop (main : Cmd) (rs rd : Stk) (rf rv : Reg) (m : Glyph) (hrd : rd ≠ rs)
    (hrv : rv ≠ rf) :
    ∀ (B l₀ : List Glyph), m ∉ B → ∀ s : State,
      s.stk rs = B ++ m :: l₀ →
      Eval main (restLoop rs rd rf rv m) s
        ((restFin rs rd rv m B l₀ s).updReg rf (Glyph.mk 2))
        (4 * (B.length + 1) + 2) :=
  _root_.Work.ConvR.Work.ConvR.eval_restLoop main rs rd rf rv m hrd hrv

end Work.ConvR
