import Mathlib
import Submission.Work.MotC2.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC2

/-- The chart-at-infinity coordinate ring `L[1/x, y/x²] = L[infU, infW]` is generated, as an
`L`-algebra, by the two elements `infU` and `infW`; hence it is a finitely generated algebra over
the field `L`, and therefore Noetherian. -/
theorem isNoetherianRing_infCoordRing (L : Type*) [Field L] (E : WeierstrassCurve L) :
    IsNoetherianRing ↥(Work.MotC2.infCoordRing E) := by
  apply isNoetherianRing_of_fg
  rw [Work.MotC2.infCoordRing]
  exact Subalgebra.fg_def.mpr ⟨{Work.MotC2.infU E, Work.MotC2.infW E},
    Set.Finite.insert _ (Set.finite_singleton _), rfl⟩

end Work.MotC2
