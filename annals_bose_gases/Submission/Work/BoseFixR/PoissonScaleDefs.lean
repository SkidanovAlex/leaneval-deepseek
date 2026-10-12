import Mathlib.Analysis.CStarAlgebra.Classes
import Submission.Work.BoseFixR.ChiR0Defs
import Submission.Work.BoseFixR.Rb5Lin.ps3_fundamentalDomain
import Submission.Work.BoseFixR.Rb5Lin.ps3_latticeBall_finite
import Submission.Work.BoseFixR.Rb5Lin.ps3_mFourier_smul
import Submission.Work.BoseFixR.Rb5Lin.ps3_torus_lift
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR

open MeasureTheory

noncomputable section

/-- The `ℤ³`-periodization of `g : ℝ³ → ℂ`: `periodZ3 g x = ∑_{d ∈ ℤ³} g (x + d)`.

(The sum is over the lattice `ℤ³` embedded in `ℝ³` as `d ↦ (d 0, d 1, d 2)`,
`Work.BoseFixR.Rb5Lin.latPoint`.) -/
def periodZ3 (g : (Fin 3 → ℝ) → ℂ) (x : Fin 3 → ℝ) : ℂ :=
  ∑' d : Fin 3 → ℤ, g (x + Rb5Lin.latPoint d)

end

end Work.BoseFixR
