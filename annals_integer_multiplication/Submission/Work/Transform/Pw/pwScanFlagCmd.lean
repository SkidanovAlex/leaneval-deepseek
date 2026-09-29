import Mathlib
import Submission.Work.Transform.pwScanDefs

namespace Work.Transform.Pw

open HvdH

/-- The flag part of the scan loop body does exactly what `flagStep` says: if `reg rGA` resp.
`reg rGB` hold the bit glyphs of `a` resp. `b`, then `flagCmd` overwrites `reg rFlag` with
`flagStep (s.reg rFlag) a b` (a difference overwrites, equal bits leave the flag unchanged),
in at most 3 steps. -/
theorem pwScanFlagCmd (main : HvdH.Cmd) (s : HvdH.State) (a b : Bool)
    (hGA : s.reg rGA = HvdH.Glyph.bit a) (hGB : s.reg rGB = HvdH.Glyph.bit b) :
    ∃ n ≤ 3, HvdH.Eval main flagCmd s
      (s.updReg rFlag (flagStep (s.reg rFlag) a b)) n := by
  cases a <;> cases b
  · have hA : ¬ (s.reg rGA = HvdH.Glyph.bit true) := by rw [hGA]; decide
    have hB : ¬ (s.reg rGB = HvdH.Glyph.bit true) := by rw [hGB]; decide
    have h3 : s.updReg rFlag (flagStep (s.reg rFlag) false false) = s := by
      simp [flagStep, HvdH.State.updReg_self]
    rw [h3]
    exact ⟨3, by norm_num, HvdH.Eval.iteF hA (HvdH.Eval.iteF hB (HvdH.Eval.skip s))⟩
  · have hA : ¬ (s.reg rGA = HvdH.Glyph.bit true) := by rw [hGA]; decide
    have h3 : s.updReg rFlag (flagStep (s.reg rFlag) false true) = s.updReg rFlag gLt := by
      simp [flagStep]
    rw [h3]
    exact ⟨3, by norm_num, HvdH.Eval.iteF hA (HvdH.Eval.iteT hGB (HvdH.Eval.set rFlag gLt s))⟩
  · have hB : ¬ (s.reg rGB = HvdH.Glyph.bit true) := by rw [hGB]; decide
    have h3 : s.updReg rFlag (flagStep (s.reg rFlag) true false) = s.updReg rFlag gGt := by
      simp [flagStep]
    rw [h3]
    exact ⟨3, by norm_num, HvdH.Eval.iteT hGA (HvdH.Eval.iteF hB (HvdH.Eval.set rFlag gGt s))⟩
  · have h3 : s.updReg rFlag (flagStep (s.reg rFlag) true true) = s := by
      simp [flagStep, HvdH.State.updReg_self]
    rw [h3]
    exact ⟨3, by norm_num, HvdH.Eval.iteT hGA (HvdH.Eval.iteT hGB (HvdH.Eval.skip s))⟩

end Work.Transform.Pw
