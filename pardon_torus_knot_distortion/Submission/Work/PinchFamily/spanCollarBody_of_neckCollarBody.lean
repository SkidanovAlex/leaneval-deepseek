import Mathlib
import Submission.Work.PinchFamily.Defs
import Submission.Work.InnermostDisk.Reduction

namespace Work.PinchFamily

open LeanEval.KnotTheory.PardonDistortion

/-- **The matched form of the collar implies the span form.**

If there is a collar `Z` of the pinch whose loops are matched, with their winding vectors, by
loops of a clean sphere `S` meeting the knot `β` fewer than `I(F,β)` times, then every loop of
`Z` has the winding vector of a loop of `S`, hence — by Pardon's Lemma, step 3
(`Work.InnermostDisk.mustbeinessential_of_cleansInSphere`) — is inessential.  So the winding span
of the collar vanishes. -/
theorem spanCollarBody_of_neckCollarBody {P : Work.CoreTopology.ParamTorus}
    (β : Work.CoreTopology.ClosedCurve P) {s : ℝ} {c : LeanEval.KnotTheory.PardonDistortion.R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} :
    Work.PinchFamily.NeckCollarBody P β s c σ u →
      Work.PinchFamily.SpanCollarBody P β s c σ u := by
  rintro ⟨Z, S, hZ, hclean, hSβ, hmatch⟩
  refine ⟨Z, hZ, ?_⟩
  rw [Work.SurgeryInvariance.WindingSpan_eq_bot_iff]
  rintro ⟨γ, hess, hγZ⟩
  obtain ⟨γ', hγ'S, hw⟩ := hmatch γ hγZ
  refine (Work.InnermostDisk.mustbeinessential_of_cleansInSphere P β S hclean hSβ γ' hγ'S) ?_
  have hess' : Work.CoreTopology.IsEssential P γ' := by
    rw [Work.SurgeryInvariance.isEssential_iff_windingOf_ne_zero] at hess ⊢
    rw [hw]
    exact hess
  exact hess'

end Work.PinchFamily
