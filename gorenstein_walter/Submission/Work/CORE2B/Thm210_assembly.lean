import Submission.Work.CORE2B.Deliverable
import Submission.Work.CORE2B.Thm210_contra_proved

/-!
# AREA CORE2B — the contract `Thm210Prop`

`Deliverable.thm210_of_contra` reduces the contract statement to `Thm210_contra`; the colleague's
`Thm210_contra_proved` supplies it (its two former obligations — `HallPerPrime`'s odd case and the
"bad configuration" `owed_bad` — are closed by the lead's design pass 18, items A and A′).
-/

open scoped MatrixGroups

set_option linter.unusedVariables false

namespace Work.CORE2B

/-- **Bender Theorem 2.10 = the contract `Work.GW2.Thm210Prop`**, complete: inputs are the toolkit
and Bender 2.6, 2.7, 2.8. -/
theorem thm210 (T : Work.GW2.LocalToolkit) (h26 : Work.GW2.Thm26Prop)
    (h27 : Work.GW2.Lemma27Prop) (h28 : Work.GW2.Lemma28Prop) : Work.GW2.Thm210Prop :=
  thm210_of_contra T h26 h27 h28 Thm210_contra_proved

end Work.CORE2B
