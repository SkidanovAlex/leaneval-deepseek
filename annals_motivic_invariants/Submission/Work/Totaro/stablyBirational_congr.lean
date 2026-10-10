import Mathlib
import Submission.Work.Totaro.Defs
import Submission.Work.K3Inputs.stablyBirat_congr
import Submission.Work.K3Inputs.StablyBiratK3
import Submission.Work.K3Inputs.not_stablyBirational_prod

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Totaro

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

/-- `Work.K3.StablyBirational` (the K3 chapter's relation, used by `Work.CY3.TotaroInput` and
`Work.K3.TotaroInput`) and the instance-free `Work.K3Inputs.StablyBirat` agree, in the form of
an equivalence of propositions.  This is the two conversions
`Work.K3Inputs.StablyBirat_to_stablyBirational` and
`Work.K3Inputs.StablyBirat_of_stablyBirational` packaged as an `↔`. -/
theorem stablyBirational_iff_stablyBirat {𝕜 : Type} [Field 𝕜] {X Y : Scheme.{0}}
    [MotivicInvariants.Variety 𝕜 X] [MotivicInvariants.Variety 𝕜 Y] :
    Work.Totaro.StablyBirational 𝕜 X Y ↔ Work.K3Inputs.StablyBirat 𝕜 X Y :=
  ⟨Work.K3Inputs.StablyBirat_of_stablyBirational (X := X) (Y := Y),
    Work.K3Inputs.StablyBirat_to_stablyBirational X Y⟩

/-- Stable birationality (`Work.Totaro.StablyBirational` = the relation used by `Work.CY3.TotaroInput` and `Work.K3.TotaroInput`) is invariant under isomorphism over `𝕜` in both variables.  With `Work.Totaro.CohSeparation.congr` this is what allows the non-stable-birationality of the two centres of one model of a link to be transferred to any other model of the same link. -/
theorem stablyBirational_congr {𝕜 : Type} [Field 𝕜]
    {X X' Y Y' : AlgebraicGeometry.Scheme.{0}}
    [MotivicInvariants.Variety 𝕜 X] [MotivicInvariants.Variety 𝕜 X']
    [MotivicInvariants.Variety 𝕜 Y] [MotivicInvariants.Variety 𝕜 Y']
    (hX : Work.Totaro.IsoOver 𝕜 X X') (hY : Work.Totaro.IsoOver 𝕜 Y Y') :
    (Work.Totaro.StablyBirational 𝕜 X Y ↔ Work.Totaro.StablyBirational 𝕜 X' Y') := by
  rw [stablyBirational_iff_stablyBirat (𝕜 := 𝕜) (X := X) (Y := Y),
    stablyBirational_iff_stablyBirat (𝕜 := 𝕜) (X := X') (Y := Y')]
  exact Work.K3Inputs.stablyBirat_congr 𝕜 (X := X) (X' := X') (Y := Y) (Y' := Y') hX hY

end

end Work.Totaro
