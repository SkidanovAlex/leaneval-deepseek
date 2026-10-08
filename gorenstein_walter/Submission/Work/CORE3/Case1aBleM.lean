import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic

namespace Work.CORE3

open Subgroup
open Work.GW2

/-- Bender 1981 §3, p. 223: `B = C_U(S) ⊆ M` for a maximal `M ⊇ N_G(P₂)`.  Deliverable
`Work.CORE3.Case1aBleMProp`.  This is the first conjunct of `Case1aMDataProp` (`hMD`), which
records the §3 `M`-analysis: `B ≤ M`, `B ∩ M = O(M)`, `U ∩ M = P₀ × (B ∩ M)`, and
`N_G(X) ≤ M` for `1 ≠ X ≤ B` (Bender's application of Lemma 2.9 to `X = B ∩ PP^g`). -/
theorem Case1aBleM (I : Case1Inputs) (hSetup : Case1aSetupProp) (hFr : Case1aFrattiniProp)
    (hAb : Case1aAbelianProp) (hA7 : Case1aA7Prop) (hMD : Case1aMDataProp) : Case1aBleMProp := by
  intro G _ _ hFT hCtx B hCase hH D P2 M hP2le hP2grp hnotdiv hCoatom hnorm
  exact (hMD G hFT hCtx B hCase hH D P2 M hP2le hP2grp hnotdiv hCoatom hnorm).1

end Work.CORE3
