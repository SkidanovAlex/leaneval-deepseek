import Mathlib
import Submission.Work.Transform.pwScanDefs
import Submission.Work.Transform.pwScanB
import Submission.Work.Transform.Pw.pwScanFlagCmd

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Work.Transform

open HvdH
open Work.Kernel
open Work.IntLib
open Work.Transform.Pw

/-- The sibling result `pwScanB` with the program *fixed* to `scanProg sA sB bA bB` (the witness
used by its proof) and without the two register hypotheses `s.reg rCont = eos`,
`s.reg rFlag = gEq`: the program's own first two commands set those registers anyway (and the proof
body of `pwScanB` never uses the hypotheses).  This is a verbatim re-run of the proof body of
`pwScanB`; the existential there hides the witness, so it cannot be extracted from its statement. -/
theorem scanProg_ev (sA sB bA bB : HvdH.Stk) :
    sA ≠ sB → bA ≠ sA → bA ≠ sB → bB ≠ sA → bB ≠ sB → bA ≠ bB →
    ∀ (main : HvdH.Cmd) (A B : List Bool) (RA RB : List HvdH.Glyph) (s : HvdH.State),
      Work.IntLib.IsBits A → Work.IntLib.IsBits B →
      s.stk sA = A.map HvdH.Glyph.bit ++ Work.Transform.Pw.gM :: RA →
      s.stk sB = B.map HvdH.Glyph.bit ++ Work.Transform.Pw.gM :: RB →
      ∃ s' n, HvdH.Eval main (Work.Transform.Pw.scanProg sA sB bA bB) s s' n ∧
        n ≤ 20 * (min A.length B.length + 1) ∧
        s'.reg Work.Transform.Pw.rCont ≠ HvdH.Glyph.eos ∧
        Work.Transform.Pw.NatFlag (s'.reg Work.Transform.Pw.rFlag)
          (Work.IntLib.ofBits A) (Work.IntLib.ofBits B) ∧
        s'.stk sA = (A.drop (min A.length B.length)).map HvdH.Glyph.bit
            ++ Work.Transform.Pw.gM :: RA ∧
        s'.stk sB = (B.drop (min A.length B.length)).map HvdH.Glyph.bit
            ++ Work.Transform.Pw.gM :: RB ∧
        s'.stk bA = ((A.take (min A.length B.length)).map HvdH.Glyph.bit).reverse
            ++ Work.Transform.Pw.gM :: s.stk bA ∧
        s'.stk bB = ((B.take (min A.length B.length)).map HvdH.Glyph.bit).reverse
            ++ Work.Transform.Pw.gM :: s.stk bB ∧
        (∀ j : HvdH.Stk, j ≠ sA → j ≠ sB → j ≠ bA → j ≠ bB → s'.stk j = s.stk j) := by
  intro hsAB hbA1 hbA2 hbB1 hbB2 hbAB
  intro main A B RA RB s hIsA hIsB hA hB
  have hAsB : sA ≠ sB := hsAB
  have hBsA : sB ≠ sA := hsAB.symm
  have hAs1 : sA ≠ bA := fun h => hbA1 h.symm
  have hs1A : bA ≠ sA := hbA1
  have hAs2 : sA ≠ bB := fun h => hbB1 h.symm
  have hs2A : bB ≠ sA := hbB1
  have hBs1 : sB ≠ bA := fun h => hbA2 h.symm
  have hs1B : bA ≠ sB := hbA2
  have hBs2 : sB ≠ bB := fun h => hbB2 h.symm
  have hs2B : bB ≠ sB := hbB2
  have hs12 : bA ≠ bB := hbAB
  have hs21 : bB ≠ bA := hbAB.symm
  let s0 : State := State.tSet s rFlag gEq
  let s1 : State := State.tSet s0 rCont Glyph.eos
  let s2 : State := State.tSet s1 rGB gM
  let s3 : State := State.tPush s2 bA rGB
  let s4 : State := State.tSet s3 rGB gM
  let s5 : State := State.tPush s4 bB rGB
  have e1 : Eval main (.set rFlag gEq) s s0 1 := eval_set main rFlag gEq s
  have e2 : Eval main (.set rCont Glyph.eos) s0 s1 1 := eval_set main rCont Glyph.eos s0
  have e3 : Eval main (.set rGB gM) s1 s2 1 := eval_set main rGB gM s1
  have e4 : Eval main (.push bA rGB) s2 s3 1 := eval_push main bA rGB s2
  have e5 : Eval main (.set rGB gM) s3 s4 1 := eval_set main rGB gM s3
  have e6 : Eval main (.push bB rGB) s4 s5 1 := eval_push main bB rGB s4
  have hs5sA : s5.stk sA = A.map Glyph.bit ++ gM :: RA := by
    have h : s5.stk sA = s.stk sA := by
      simp only [s5, s4, s3, s2, s1, s0, State.tPush, State.tSet, State.updStk, State.updReg,
        Function.update_apply, Function.update_self]
      simp_all
    rw [h, hA]
  have hs5sB : s5.stk sB = B.map Glyph.bit ++ gM :: RB := by
    have h : s5.stk sB = s.stk sB := by
      simp only [s5, s4, s3, s2, s1, s0, State.tPush, State.tSet, State.updStk, State.updReg,
        Function.update_apply, Function.update_self]
      simp_all
    rw [h, hB]
  have hs5bA : s5.stk bA = gM :: s.stk bA := by
    simp only [s5, s4, s3, s2, s1, s0, State.tPush, State.tSet, State.updStk, State.updReg,
      Function.update_apply, Function.update_self]
    simp_all
  have hs5bB : s5.stk bB = gM :: s.stk bB := by
    simp only [s5, s4, s3, s2, s1, s0, State.tPush, State.tSet, State.updStk, State.updReg,
      Function.update_apply, Function.update_self]
    simp_all
  have hs5c : s5.reg rCont = Glyph.eos := by
    simp only [s5, s4, s3, s2, s1, s0, State.tPush, State.tSet, State.updStk, State.updReg,
      Function.update_apply, Function.update_self]
    simp_all [rGB_ne_rCont, rCont_ne_rGB]
  have hs5f : s5.reg rFlag = flagOf (ofBits (A.take 0)) (ofBits (B.take 0)) := by
    simp only [s5, s4, s3, s2, s1, s0, State.tPush, State.tSet, State.updStk, State.updReg,
      Function.update_apply, Function.update_self, List.take_zero, ofBits]
    simp_all [rGB_ne_rFlag, rFlag_ne_rGB, rFlag_ne_rCont, flagOf_zero_zero]
  obtain ⟨s', n, hev, hn, hcont, hflag, htA, htB, htbA, htbB, hoth⟩ :=
    scanAux main sA sB bA bB hsAB hbA1 hbA2 hbB1 hbB2 hbAB (min A.length B.length) A B 0
      RA RB (s.stk bA) (s.stk bB) s5 hIsA hIsB (Nat.zero_le _) (by simp) hs5sA hs5sB
      (by simpa using hs5bA) (by simpa using hs5bB) hs5c hs5f
  have hev0 : Eval main (scanProg sA sB bA bB) s s'
      (1 + (1 + (1 + (1 + (1 + (1 + n)))))) :=
    Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5 (Eval.seq e6 hev)))))
  refine ⟨s', 1 + (1 + (1 + (1 + (1 + (1 + n))))), hev0, by omega, hcont, hflag, htA, htB,
    ?_, ?_, ?_⟩
  · exact htbA
  · exact htbB
  · intro j hj1 hj2 hj3 hj4
    rw [hoth j hj1 hj2 hj3 hj4]
    simp only [s5, s4, s3, s2, s1, s0, State.tPush, State.tSet, State.updStk, State.updReg,
      Function.update_apply, Function.update_self]
    simp_all


/-- Buffered lockstep comparison of two canonical bit strings, run by the already-defined program
`Work.Transform.Pw.scanProg sA sB bA bB` (`Submission.Work.Transform.pwScanDefs`).

`A` (least significant bit first) sits above the frame marker `Work.Transform.Pw.gM` on stack `sA`,
`B` likewise on stack `sB`.  The program peeks both stacks; while both hold a bit it pops one bit
from each (pushing it onto the buffer stack `bA` resp. `bB`, above a fresh `gM` that the program
pushes) and updates the flag `reg Pw.rFlag` so that a difference overwrites the flag and equal bits
leave it (the last, i.e. most significant, difference wins); as soon as one side has reached its
marker it sets the flag (`gLt` when `A` is exhausted first, `gGt` when `B` is, keeping the
accumulated flag when both are exhausted simultaneously) and stops (`reg Pw.rCont` leaves `eos`).

With `k = min A.length B.length` this leaves the unconsumed parts on `sA`/`sB`, the consumed
prefixes (reversed) above a fresh `gM` on the buffers, sets
`NatFlag (reg rFlag) (ofBits A) (ofBits B)`, and costs at most `K * (k + 1)` steps.  The bound is
deliberately *tight*: it must not mention `A.length + B.length` (an element compared against a much
longer stored maximum has to cost only the element's own length).  Note the loop must *not* pop the
marker-side glyph of a string that is exhausted.

Hint: the module `Submission.Work.Transform.pwScanB` already proves the sibling result
`Work.Transform.pwScanB`, which is identical except that the program is given existentially and two
extra (unused) register hypotheses `s.reg rCont = eos`, `s.reg rFlag = gEq` are assumed; its proof
witness is `scanProg sA sB bA bB` with K = 20, so the claim below is a strict weakening and that
proof body can be reused verbatim. -/
theorem pwScanBv (sA sB bA bB : HvdH.Stk) :
    sA ≠ sB → bA ≠ sA → bA ≠ sB → bB ≠ sA → bB ≠ sB → bA ≠ bB →
    ∃ (K : ℕ),
    ∀ (main : HvdH.Cmd) (A B : List Bool) (RA RB : List HvdH.Glyph) (s : HvdH.State),
      Work.IntLib.IsBits A → Work.IntLib.IsBits B →
      s.stk sA = A.map HvdH.Glyph.bit ++ Work.Transform.Pw.gM :: RA →
      s.stk sB = B.map HvdH.Glyph.bit ++ Work.Transform.Pw.gM :: RB →
      ∃ s' n, HvdH.Eval main (Work.Transform.Pw.scanProg sA sB bA bB) s s' n ∧
        n ≤ K * (min A.length B.length + 1) ∧
        s'.reg Work.Transform.Pw.rCont ≠ HvdH.Glyph.eos ∧
        Work.Transform.Pw.NatFlag (s'.reg Work.Transform.Pw.rFlag)
          (Work.IntLib.ofBits A) (Work.IntLib.ofBits B) ∧
        s'.stk sA = (A.drop (min A.length B.length)).map HvdH.Glyph.bit
            ++ Work.Transform.Pw.gM :: RA ∧
        s'.stk sB = (B.drop (min A.length B.length)).map HvdH.Glyph.bit
            ++ Work.Transform.Pw.gM :: RB ∧
        s'.stk bA = ((A.take (min A.length B.length)).map HvdH.Glyph.bit).reverse
            ++ Work.Transform.Pw.gM :: s.stk bA ∧
        s'.stk bB = ((B.take (min A.length B.length)).map HvdH.Glyph.bit).reverse
            ++ Work.Transform.Pw.gM :: s.stk bB ∧
        (∀ j : HvdH.Stk, j ≠ sA → j ≠ sB → j ≠ bA → j ≠ bB → s'.stk j = s.stk j) := by
  intro hsAB hbA1 hbA2 hbB1 hbB2 hbAB
  exact ⟨20, scanProg_ev sA sB bA bB hsAB hbA1 hbA2 hbB1 hbB2 hbAB⟩

end Work.Transform
