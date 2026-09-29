import Mathlib
import Submission.Work.Kernel.ifZeroDefs
import Submission.Work.Kernel.Raw

namespace Work.Kernel

open HvdH

/-!
# Kernel: the `ifZero` drain loop

`ifZero_drain r = set r Glyph.eos ;; loop r Glyph.eos (pop 0 r ;; ite r Glyph.iend skip (set r Glyph.eos))`
runs from a state whose stack `0` starts with the bits of a positive integer followed by `iend`:
it pops the bits one at a time, and stops as soon as it has popped (and left in `r`) the `iend`.
The main lemma `Work.Kernel.ifZeroDrain` proves that it consumes exactly `ms.map Glyph.bit`
followed by one `Glyph.iend`, leaving stack `0 = R` and `r = Glyph.iend`, at cost
`4 * (ms.length + 1) + 2`.

The proof is a straight-line evaluation for the initial `set`, followed by an induction on `ms`
that unrolls the `loop` with `Eval.loopT` (`4` per iteration = `3` for the body plus `1` for the
loop test, plus `1` for the final failing test).
-/

/-- A bit glyph is never `iend`. -/
theorem ifZeroDrain_bit_ne_iend (b : Bool) : Glyph.bit b ≠ Glyph.iend := by
  intro h; cases h

/-! ## `pop` at stack `0` -/

/-- `pop 0 r` on a stack starting with `bit b`. -/
theorem ifZeroDrain_pop_bit (main : Cmd) (r : Reg) (b : Bool) (A : List Glyph) (s : State)
    (hstk : s.stk 0 = Glyph.bit b :: A) :
    Eval main (Cmd.pop 0 r) s ((s.updStk 0 A).updReg r (Glyph.bit b)) 1 := by
  have h := Eval.pop (main := main) 0 r s
  rw [hstk] at h
  simp only [List.headD_cons, List.tail_cons] at h
  show Eval main (Cmd.pop 0 r) s
    ⟨Function.update s.reg r (Glyph.bit b), Function.update s.stk 0 A⟩ 1
  exact h

/-- `pop 0 r` on a stack starting with `iend`. -/
theorem ifZeroDrain_pop_iend (main : Cmd) (r : Reg) (A : List Glyph) (s : State)
    (hstk : s.stk 0 = Glyph.iend :: A) :
    Eval main (Cmd.pop 0 r) s ((s.updStk 0 A).updReg r Glyph.iend) 1 := by
  have h := Eval.pop (main := main) 0 r s
  rw [hstk] at h
  simp only [List.headD_cons, List.tail_cons] at h
  show Eval main (Cmd.pop 0 r) s
    ⟨Function.update s.reg r Glyph.iend, Function.update s.stk 0 A⟩ 1
  exact h

/-! ## The final state ignores what the body did to stack `0` and to `r` -/

/-- `ifZero_drainState` overwrites both stack `0` and register `r`. -/
theorem ifZeroDrain_state_updReg (r : Reg) (R : List Glyph) (s : State) (g : Glyph) :
    ifZero_drainState r R (s.updReg r g) = ifZero_drainState r R s := by
  simp [ifZero_drainState, State.updStk, State.updReg]

theorem ifZeroDrain_state_updStk (r : Reg) (R : List Glyph) (s : State) (A : List Glyph) :
    ifZero_drainState r R (s.updStk 0 A) = ifZero_drainState r R s := by
  simp [ifZero_drainState, State.updStk, State.updReg]

/-! ## One iteration of the loop -/

/-- The loop body on a stack starting with `bit b`: the bit is popped and `r` is reset to `eos`
(so the loop test still succeeds). -/
theorem ifZeroDrain_body_bit (main : Cmd) (r : Reg) (b : Bool) (A : List Glyph) (s : State)
    (hstk : s.stk 0 = Glyph.bit b :: A) :
    Eval main (ifZero_drainBody r) s ((s.updStk 0 A).updReg r Glyph.eos) 3 := by
  have hpop := ifZeroDrain_pop_bit main r b A s hstk
  have hreg : ((s.updStk 0 A).updReg r (Glyph.bit b)).reg r = Glyph.bit b := by
    simp [State.updReg]
  have hne : ((s.updStk 0 A).updReg r (Glyph.bit b)).reg r ≠ Glyph.iend := by
    rw [hreg]; exact ifZeroDrain_bit_ne_iend b
  have hset : Eval main (Cmd.set r Glyph.eos) ((s.updStk 0 A).updReg r (Glyph.bit b))
      (((s.updStk 0 A).updReg r (Glyph.bit b)).updReg r Glyph.eos) 1 := Eval.set r Glyph.eos _
  have hite : Eval main (Cmd.ite r Glyph.iend Cmd.skip (Cmd.set r Glyph.eos))
      ((s.updStk 0 A).updReg r (Glyph.bit b))
      (((s.updStk 0 A).updReg r (Glyph.bit b)).updReg r Glyph.eos) 2 := Eval.iteF hne hset
  have hseq := Eval.seq hpop hite
  rw [ifZero_drainBody]
  show Eval main (Cmd.seq (Cmd.pop 0 r) (Cmd.ite r Glyph.iend Cmd.skip (Cmd.set r Glyph.eos))) s
    ((s.updStk 0 A).updReg r Glyph.eos) 3
  simpa [State.updReg_updReg] using hseq

/-- The loop body on a stack starting with `iend`: the `iend` stays in `r`, so the loop test fails
and the loop stops. -/
theorem ifZeroDrain_body_iend (main : Cmd) (r : Reg) (A : List Glyph) (s : State)
    (hstk : s.stk 0 = Glyph.iend :: A) :
    Eval main (ifZero_drainBody r) s ((s.updStk 0 A).updReg r Glyph.iend) 3 := by
  have hpop := ifZeroDrain_pop_iend main r A s hstk
  have hreg : ((s.updStk 0 A).updReg r Glyph.iend).reg r = Glyph.iend := by
    simp [State.updReg]
  have hskip : Eval main Cmd.skip ((s.updStk 0 A).updReg r Glyph.iend)
      ((s.updStk 0 A).updReg r Glyph.iend) 1 := Eval.skip _
  have hite : Eval main (Cmd.ite r Glyph.iend Cmd.skip (Cmd.set r Glyph.eos))
      ((s.updStk 0 A).updReg r Glyph.iend) ((s.updStk 0 A).updReg r Glyph.iend) 2 :=
    Eval.iteT hreg hskip
  have hseq := Eval.seq hpop hite
  rw [ifZero_drainBody]
  show Eval main (Cmd.seq (Cmd.pop 0 r) (Cmd.ite r Glyph.iend Cmd.skip (Cmd.set r Glyph.eos))) s
    ((s.updStk 0 A).updReg r Glyph.iend) 3
  exact hseq

/-! ## The loop -/

/-- The drain loop consumes `ms.map Glyph.bit` followed by one `Glyph.iend`, starting from a state
whose register `r` holds `eos` (the loop test constant).  Cost: `3` per iteration for the body, `1`
for each loop test (including the last, failing one), so `4 * (ms.length + 1) + 1`. -/
theorem ifZeroDrain_loop (main : Cmd) (r : Reg) (R : List Glyph) :
    ∀ (ms : List Bool) (s : State),
      s.stk 0 = ms.map Glyph.bit ++ Glyph.iend :: R →
      s.reg r = Glyph.eos →
      Eval main (ifZero_drainLoop r) s (ifZero_drainState r R s) (4 * (ms.length + 1) + 1) := by
  intro ms
  induction ms with
  | nil =>
    intro s hstk hreg
    have hstk' : s.stk 0 = Glyph.iend :: R := by simpa using hstk
    have hbody : Eval main (ifZero_drainBody r) s (ifZero_drainState r R s) 3 :=
      ifZeroDrain_body_iend main r R s hstk'
    have hstop : (ifZero_drainState r R s).reg r ≠ Glyph.eos := by simp [ifZero_drainState]
    have hloop := Eval.loopT (main := main) hreg hbody (Eval.loopF (main := main) hstop)
    rw [ifZero_drainLoop]
    show Eval main (Cmd.loop r Glyph.eos (ifZero_drainBody r)) s (ifZero_drainState r R s) 5
    exact hloop
  | cons b ms' ih =>
    intro s hstk hreg
    have hstk' : s.stk 0 = Glyph.bit b :: (ms'.map Glyph.bit ++ Glyph.iend :: R) := by
      simpa using hstk
    have hbody : Eval main (ifZero_drainBody r) s
        ((s.updStk 0 (ms'.map Glyph.bit ++ Glyph.iend :: R)).updReg r Glyph.eos) 3 :=
      ifZeroDrain_body_bit main r b _ s hstk'
    have hmidstk : ((s.updStk 0 (ms'.map Glyph.bit ++ Glyph.iend :: R)).updReg r Glyph.eos).stk 0
        = ms'.map Glyph.bit ++ Glyph.iend :: R := by simp
    have hmidreg : ((s.updStk 0 (ms'.map Glyph.bit ++ Glyph.iend :: R)).updReg r Glyph.eos).reg r
        = Glyph.eos := by simp [State.updReg]
    have hih := ih _ hmidstk hmidreg
    have hloop := Eval.loopT (main := main) hreg hbody hih
    have hs1 := ifZeroDrain_state_updReg r R
      (s.updStk 0 (ms'.map Glyph.bit ++ Glyph.iend :: R)) Glyph.eos
    have hs2 := ifZeroDrain_state_updStk r R s (ms'.map Glyph.bit ++ Glyph.iend :: R)
    rw [hs1, hs2] at hloop
    rw [ifZero_drainLoop]
    have hc : 3 + (4 * (ms'.length + 1) + 1) + 1 = 4 * ((b :: ms').length + 1) + 1 := by
      simp [List.length_cons]; ring
    rw [hc] at hloop
    exact hloop

/-- `import Submission.Work.Kernel.ifZeroDefs` and `Submission.Work.Kernel.Raw`, work in `namespace Work.Kernel` (with `open HvdH`).  `ifZero_drain`/`ifZero_drainState` are defined in `Submission/Work/Kernel/ifZeroDefs.lean`: `ifZero_drain r = set r Glyph.eos ;; loop r Glyph.eos (pop 0 r ;; ite r Glyph.iend skip (set r Glyph.eos))` and `ifZero_drainState r R s = (s.updStk 0 R).updReg r Glyph.iend`.  Prove that it consumes exactly the `ms.map bit` glyphs followed by one `iend`, leaving stack 0 = `R`, register `r` = `iend`, everything else untouched, at cost `4 * (ms.length + 1) + 2`.  Helpers in this file must be named with the prefix `ifZeroDrain_`. -/
theorem ifZeroDrain (main : HvdH.Cmd) (r : HvdH.Reg) (ms : List Bool) (R : List HvdH.Glyph)
    (s : HvdH.State) (hstk : s.stk 0 = ms.map HvdH.Glyph.bit ++ HvdH.Glyph.iend :: R) :
    HvdH.Eval main (ifZero_drain r) s (ifZero_drainState r R s) (4 * (ms.length + 1) + 2) := by
  have hset : Eval main (Cmd.set r Glyph.eos) s (s.updReg r Glyph.eos) 1 := Eval.set r Glyph.eos s
  have hloop := ifZeroDrain_loop main r R ms (s.updReg r Glyph.eos) (by simpa using hstk) (by simp)
  have hstate := ifZeroDrain_state_updReg r R s Glyph.eos
  rw [hstate] at hloop
  have hmain : Eval main (Cmd.seq (Cmd.set r Glyph.eos) (ifZero_drainLoop r)) s
      (ifZero_drainState r R s) (1 + (4 * (ms.length + 1) + 1)) := Eval.seq hset hloop
  have hc : 1 + (4 * (ms.length + 1) + 1) = 4 * (ms.length + 1) + 2 := by ring
  rw [hc] at hmain
  rw [ifZero_drain]
  exact hmain

end Work.Kernel
