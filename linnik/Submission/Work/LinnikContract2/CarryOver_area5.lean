import Mathlib
import Submission.Work.LinnikAreas.area5
import Submission.Work.LinnikContract2.Areas

set_option linter.unusedVariables false

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikContract2

/-- **AREA 5 (round 2), proved.**  HB Lemma 13.3, uniform in `λ ∈ [0,R]`: transported from the
round-1 proof `Work.LinnikAreas.area5`, since `Area1`, `PerCharCert`, `boxAbs`, `Bfun`, `IsZ` and
`lamOf` are unchanged between the editions. -/
theorem area5 : Area5 := Work.LinnikAreas.area5


end Work.LinnikContract2
