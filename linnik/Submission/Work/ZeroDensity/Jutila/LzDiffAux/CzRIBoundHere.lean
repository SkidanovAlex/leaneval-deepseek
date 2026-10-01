import Mathlib
import Submission.Work.ZeroDensity.Jutila.BzCross.CzRIAux
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.KappaMertensHere
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.CzMertBoundHere
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.CzRowBoundHere
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.CzSigmaTsumHere
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.CzHarmDecayHere

/-! Region I of the two-sided `S₃` boundary term is `O(N)`: re-homing of
`BzCross.czRI_bound.lean` into `LzDiffAux`, with the five leaf inputs supplied by the local
lemmas `CzMertBoundHere`, `CzRowBoundHere`, `CzSigmaTsumHere`, `CzHarmDecayHere` and with the
Mertens package `KappaMertensHere` in place of the `KappaMertensInput` hypothesis. -/

namespace Work.ZeroDensity.Jutila.LzDiffAux

open Finset
open Work.ZeroDensity.Jutila
open Work.ZeroDensity.Jutila.BzCross

noncomputable section

/-- **Region I of the two-sided `S₃` boundary term is `O(N)`.** -/
theorem CzRIBoundHere : ∃ C : ℝ, 0 < C ∧ ∀ (w y : ℝ) (N : ℕ),
    1 ≤ w → w ≤ y → y ≤ (N : ℝ) → (N : ℝ) < w * y → |czRI w y N| ≤ C * (N : ℝ) := by
  obtain ⟨CM, cM, hCM, hcM, hM⟩ := CzMertBoundHere
  obtain ⟨CR, cR, hCR, hcR, hRow⟩ := CzRowBoundHere Work.ZeroDensity.Jutila.LzDiffAux.KappaMertensHere
  obtain ⟨CS, hCS, hSig⟩ := CzSigmaTsumHere cR hcR
  obtain ⟨CH1, hCH1, hHarm1⟩ := CzHarmDecayHere cM hcM
  obtain ⟨CH2, hCH2, hHarm2⟩ := CzHarmDecayHere cR hcR
  refine czRI_bound_aux CM cM hCM hcM ?_ CR cR hCR hcR ?_ CS hCS ?_ CH1 hCH1 ?_ CH2 hCH2 ?_
  · intro T hT
    simpa only [czEps] using hM T hT
  · intro w y N q t hw1 hwy hyN hNwy hq1 hqQ ht hsq
    exact hRow hw1 hwy hyN hNwy hq1 hqQ ht hsq
  · intro a T ha hT
    simpa only [czSig, czEps] using hSig a T ha hT
  · intro A Q hA hQ
    simpa only [czEps] using hHarm1 A Q hA hQ
  · intro A Q hA hQ
    simpa only [czEps] using hHarm2 A Q hA hQ

end

end Work.ZeroDensity.Jutila.LzDiffAux
