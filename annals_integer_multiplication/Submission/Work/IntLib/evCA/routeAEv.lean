import Mathlib
import Submission.Work.IntLib.evCarryDefs
import Submission.Work.IntLib.evCA.routeASem
import Submission.Work.IntLib.evCA.accPSuccLow
import Submission.Work.IntLib.evCA.accPSuccHigh

/-!
# `IntLib` / `evCA`: the routing phase of one ripple-addition step

`EvC.routeA` is the second phase of the body of the `evCarryAdd` addition loop.  After the first
phase (`EvC.stepA`) has computed the sum bit

`x k = sumBit (W.getD k false) (hbits.getD k false) (carryC W hbits false k)`

and left it in the register `rSa`, `routeA` decides *where* that bit goes: while the unary counter
on `aCW` still has units (`k < b`) the bit is a low bit and is pushed onto the accumulator `aO`,
consuming one counter unit; once the counter is exhausted (`b ≤ k`) the bit is a high bit and is
pushed onto the scratch stack `a2` instead.

This file assembles the phase lemma from two independent facts:

* `routeASem` — the raw semantics of `routeA` (both branches, cost `≤ 4`, frame);
* `accPSuccLow` / `accPSuccHigh` — the arithmetic half: in either branch the accumulator predicate
  `EvC.accP` advances from `k` to `k + 1`.
-/

set_option autoImplicit false

namespace Work.IntLib.evCA

open HvdH

/-- A positive unary counter has head `gTok`. -/
theorem Unary_headD_gTok {v : ℕ} (hv : v ≠ 0) (rest : List HvdH.Glyph) :
    (Unary v rest).headD HvdH.Glyph.eos = gTok := by
  cases v with
  | zero => exact absurd rfl hv
  | succ v =>
      show (Unary (v + 1) rest).headD HvdH.Glyph.eos = gTok
      rw [Unary_succ]
      rfl

theorem routeAEv (main : HvdH.Cmd) (b : ℕ) (W hbits LO : List Bool)
    (Os A2s Cs : List HvdH.Glyph) (k : ℕ) (s : HvdH.State)
    (hacc : Work.IntLib.EvC.accP b W hbits LO Os A2s Cs k s)
    (hs : s.reg Work.IntLib.EvC.rSa = HvdH.Glyph.bit
      (Work.IntLib.EvC.sumBit (W.getD k false) (hbits.getD k false) (Work.IntLib.EvC.carryC W hbits false k))) :
    ∃ (s' : HvdH.State) (n : ℕ),
      Work.Layout.Ev main Work.IntLib.EvC.routeA s s' n ∧ n ≤ 6 ∧
      Work.IntLib.EvC.accP b W hbits LO Os A2s Cs (k + 1) s' ∧
      (∀ j : HvdH.Stk, j ≠ Work.IntLib.aO → j ≠ Work.IntLib.a2 → j ≠ Work.IntLib.aCW →
        s'.stk j = s.stk j) := by
  have hacc0 := hacc
  simp only [Work.IntLib.EvC.accP] at hacc0
  obtain ⟨hO, h2s, hCW⟩ := hacc0
  obtain ⟨s', n, hEv, hn, hlow, hhigh, hfr⟩ := routeASem main s
  have hbit : HvdH.Glyph.bit (Work.IntLib.EvC.sumBit (W.getD k false) (hbits.getD k false)
      (Work.IntLib.EvC.carryC W hbits false k)) = s.reg Work.IntLib.EvC.rSa := hs.symm
  rcases lt_or_ge k b with hkb | hbk
  · -- the counter is still positive: the sum bit is a low bit, pushed onto `aO`
    have hbne : b - k ≠ 0 := by omega
    have hhead : (s.stk Work.IntLib.aCW).headD HvdH.Glyph.eos = Work.IntLib.gTok := by
      rw [hCW]
      exact Unary_headD_gTok hbne (Shift.gmk Work.IntLib.aCW :: Cs)
    obtain ⟨h1, h2, h3⟩ := hlow hhead
    refine ⟨s', n, hEv, by omega, ?_, hfr⟩
    refine accPSuccLow b W hbits LO Os A2s Cs k s s' hkb hacc ?_ h2 h3
    rw [h1, hbit]
  · -- the counter is exhausted: the sum bit is a high bit, pushed onto `a2`
    have hbk0 : b - k = 0 := Nat.sub_eq_zero_of_le hbk
    have hhead : (s.stk Work.IntLib.aCW).headD HvdH.Glyph.eos ≠ Work.IntLib.gTok := by
      rw [hCW, hbk0, Unary_zero]
      exact Work.IntLib.gEnd_ne_gTok
    obtain ⟨h1, h2, h3⟩ := hhigh hhead
    refine ⟨s', n, hEv, by omega, ?_, hfr⟩
    refine accPSuccHigh b W hbits LO Os A2s Cs k s s' hbk hacc h1 ?_ h3
    rw [h2, hbit]

end Work.IntLib.evCA
