import Mathlib
import Submission.Work.MotK.CensusFibre.SecPolarDefs
import Submission.Work.MotK.KleinData
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 0

namespace Work.MotK.CensusFibre

/-- The polar expansion of the secant quintic `s = kleinSec`: the substitution `x = c + t • u`
turns `s` into the polynomial `∑_{j ≤ 5} t^j * (kleinSecP j a b c u)` in `t`. -/
theorem sec_polar_expansion (R : Type*) [CommRing R] (a b : R) (c u : Fin 5 → R) (t : R) :
    Work.MotK.kleinSec a b (fun i => c i + t * u i)
      = Work.MotK.kleinSecP0 a b c u + t * Work.MotK.kleinSecP1 a b c u
        + t ^ 2 * Work.MotK.kleinSecP2 a b c u + t ^ 3 * Work.MotK.kleinSecP3 a b c u
        + t ^ 4 * Work.MotK.kleinSecP4 a b c u + t ^ 5 * Work.MotK.kleinSecP5 a b c u := by
  simp only [Work.MotK.kleinSec, Work.MotK.kleinSecP0, Work.MotK.kleinSecP1, Work.MotK.kleinSecP2,
    Work.MotK.kleinSecP3, Work.MotK.kleinSecP4, Work.MotK.kleinSecP5]
  first | refl_ring1 | ring

end Work.MotK.CensusFibre
