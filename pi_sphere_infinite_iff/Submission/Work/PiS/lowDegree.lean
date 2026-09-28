import Mathlib
import Submission.Work.PiS.Interfaces
import Submission.Work.RatHurewicz.SphereConnectivity

/-!
# Area LOW: `π₀(Sⁿ) = *` for `n ≥ 1` and `π₁(Sⁿ) = 1` for `n ≥ 2`

Both halves are the connectivity of the sphere `Work.RatHurewicz.SphereConnected` (proved in the
area STEMS) read at `j = 0` and `j = 1`.
-/

set_option autoImplicit false

namespace Work.PiS

open scoped Topology

theorem lowDegree : Work.PiS.LowDegree := by
  constructor
  · intro n hn
    have h := Work.RatHurewicz.sphereConnected n hn (pt n) 0 (by omega)
    simpa [HomotopyGroup.Pi, Sph] using h
  · intro n hn
    have h := Work.RatHurewicz.sphereConnected n (by omega) (pt n) 1 (by omega)
    simpa [HomotopyGroup.Pi, Sph] using h

end Work.PiS
