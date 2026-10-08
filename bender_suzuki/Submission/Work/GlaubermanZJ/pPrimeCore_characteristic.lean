import Mathlib
import Submission.Work.GlaubermanZJ.Basic
import Submission.Work.GlaubermanZJ.pPrimeCore_eq_fitting

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.GlaubermanZJ

/-- The blueprint's `O_{p'}(G)` (supremum of the normal subgroups of order coprime to `p`)
coincides, for `p` prime, with the Feit–Thompson project's `π`-core
`Work.Fitting.pPrimeCore p G = O_{p'}(G) = sSup {N | N.Normal, IsPiNat (· ≠ p) (card N)}`
(`pPrimeCore_eq_fitting`).  The latter is a `sSup` of an automorphism-invariant family, hence
characteristic (`Work.Fitting.piCore_characteristic`), and so is `O_{p'}(G)`. -/
theorem pPrimeCore_characteristic {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) :
    (Submission.Blueprint.pPrimeCore p G).Characteristic := by
  rw [pPrimeCore_eq_fitting p hp]
  exact Work.Fitting.pPrimeCore_characteristic p G

end Work.GlaubermanZJ
