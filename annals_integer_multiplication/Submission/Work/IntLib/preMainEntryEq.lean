import Mathlib
import Submission.Work.IntLib.chunkProg

namespace Work.IntLib

open HvdH

/-- The push order of the `chunk` loop at `k = 0` is empty: this is what makes stack `sS` of the
loop entry state `lStk x b N Y 0` carry only its frame marker. -/
theorem outOrder_zero_preMainEq (ps : List Bool) (b : ℕ) : outOrder ps b 0 = [] := by
  simp [outOrder, Nat.zero_div, Nat.zero_mod]

/-- The pre-loop entry state of the `chunk` word, read off from the stack hypotheses `hX … hZ, h0,
hoth`: the registers are all `eos` and the stacks are exactly `lStk x b N (Yinit b N X₀) 0`.

This is a pure bookkeeping lemma: every one of the eleven stacks singled out by `hX … hZ, h0` is
matched against its defining clause of `lStk`/`Yinit` at `k = 0` (`cg x 0 = 0`, `wcnt b 0 = 0`,
`0 / b = 0`, `outOrder _ b 0 = []`), and the remaining stacks (`1, 2, 13, 14, 15`) are covered by
`hoth` together with `Yinit_other`. -/
theorem preMainEntryEq (x b N : ℕ) (X₀ : HvdH.Stk → List HvdH.Glyph) (s : HvdH.State)
    (hreg : ∀ r : HvdH.Reg, s.reg r = HvdH.Glyph.eos)
    (hX : s.stk Work.IntLib.sX = Work.IntLib.streamOf x ++ Work.IntLib.Shift.gmk Work.IntLib.sX :: X₀ Work.IntLib.sX)
    (hB : s.stk Work.IntLib.sB = HvdH.Val.enc (HvdH.Val.int (b : ℤ)) ++ Work.IntLib.Shift.gmk Work.IntLib.sB :: X₀ Work.IntLib.sB)
    (hN : s.stk Work.IntLib.sN = HvdH.Val.enc (HvdH.Val.int (N : ℤ)) ++ Work.IntLib.Shift.gmk Work.IntLib.sN :: X₀ Work.IntLib.sN)
    (hR : s.stk Work.IntLib.sR = [HvdH.Glyph.pos] ++ Work.IntLib.Shift.gmk Work.IntLib.sR :: X₀ Work.IntLib.sR)
    (hS : s.stk Work.IntLib.sS = Work.IntLib.Shift.gmk Work.IntLib.sS :: X₀ Work.IntLib.sS)
    (hCW : s.stk Work.IntLib.sCW = Work.IntLib.gEnd :: Work.IntLib.Shift.gmk Work.IntLib.sCW :: X₀ Work.IntLib.sCW)
    (hCB : s.stk Work.IntLib.sCB = Work.IntLib.Unary b (Work.IntLib.Shift.gmk Work.IntLib.sCB :: X₀ Work.IntLib.sCB))
    (hCT : s.stk Work.IntLib.sCT = Work.IntLib.Shift.gmk Work.IntLib.sCT :: X₀ Work.IntLib.sCT)
    (hCN : s.stk Work.IntLib.sCN = Work.IntLib.Unary N (Work.IntLib.Shift.gmk Work.IntLib.sCN :: X₀ Work.IntLib.sCN))
    (hZ : s.stk Work.IntLib.sZ = Work.IntLib.Shift.gmk Work.IntLib.sZ :: X₀ Work.IntLib.sZ)
    (h0 : s.stk 0 = X₀ 0)
    (hoth : ∀ j : HvdH.Stk, j ≠ 0 → j ≠ Work.IntLib.sX → j ≠ Work.IntLib.sB → j ≠ Work.IntLib.sN →
      j ≠ Work.IntLib.sR → j ≠ Work.IntLib.sS → j ≠ Work.IntLib.sCW → j ≠ Work.IntLib.sCB →
      j ≠ Work.IntLib.sCT → j ≠ Work.IntLib.sCN → j ≠ Work.IntLib.sZ → s.stk j = X₀ j) :
    s = ⟨fun _ => HvdH.Glyph.eos, Work.IntLib.lStk x b N (Work.IntLib.Yinit b N X₀) 0⟩ := by
  have key : ∀ j : Stk, s.stk j = lStk x b N (Yinit b N X₀) 0 j := by
    intro j
    -- normalise the stack constants so that the hypotheses match the `fin_cases` numerals
    simp only [sX, sB, sN, sR, sS, sCW, sCB, sCT, sCN, sZ] at hX hB hN hR hS hCW hCB hCT hCN hZ h0 hoth
    fin_cases j <;>
      simp [lStk, Yinit, sX, sB, sN, sR, sS, sCW, sCB, sCT, sCN, sZ, cg, wcnt, Unary,
        outOrder_zero_preMainEq, hX, hB, hN, hR, hS, hCW, hCB, hCT, hCN, hZ, h0, hoth]
  cases s
  simp only [State.mk.injEq]
  exact ⟨funext fun r => hreg r, funext key⟩

end Work.IntLib
