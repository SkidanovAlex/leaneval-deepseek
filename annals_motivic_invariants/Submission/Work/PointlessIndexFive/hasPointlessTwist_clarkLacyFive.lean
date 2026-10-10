import Mathlib
import Submission.Work.PointlessIndexFive.Defs
import Submission.Work.PointlessIndexFive.period_eq_five_of_pointless
import Submission.Work.TorsorExistence.period_toTorsor_eq_five_iff

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.PointlessIndexFive

/-- The sharp arithmetic residual `HasPointlessTwist 𝕜` implies the Arithmetic area's named input
`Work.Arithmetic.ClarkLacyFive 𝕜` (`∃ T : Torsor 𝕜, T.period = 5`): a pointless quintic twist is
a Weil–Châtelet class of period `5`. -/
theorem hasPointlessTwist_clarkLacyFive {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (h : HasPointlessTwist 𝕜) : Work.Arithmetic.ClarkLacyFive 𝕜 := by
  obtain ⟨D, hD⟩ := h
  exact ⟨D.toTorsor, period_eq_five_of_pointless D hD⟩

end Work.PointlessIndexFive
