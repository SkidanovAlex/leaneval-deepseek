import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.sec2CtxOfBGData

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
/-- **Bridge `D ↦ C`**: the centralizer-splitting hypothesis produces, for every
Bender–Glauberman datum `D : Work.GW2.BGData G`, a §2 context `C : Work.BG.Sec2Ctx G`
compatible with `D` (`C.P.H = D.H`, `C.P.U = D.U`, `C.P.H0 = H₁ = U S₀`, `C.t = D.t`,
`C.s = D.t₁`).  This is the `∃`-form of `Work.BG.sec2CtxOfBGData` packaged as the
structure `Work.GW2.C16.Compat`. -/
theorem bridge (hSplit : Work.GW2.CentralizerSplitProp) : Work.GW2.C16.BridgeProp := by
  intro G _ _ D
  obtain ⟨C, hH, hU, hH0, ht, hs⟩ := sec2CtxOfBGData hSplit D
  exact ⟨C, hH, hU, hH0, ht, hs⟩

end Work.BG
