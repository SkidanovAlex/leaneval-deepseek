import Mathlib
import Submission.Work.BW.basisRed_defs
import Submission.Work.BW.basisRed_exists_indep

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Auxiliary vocabulary for the flag of successive minima

`Work.BW.Minkowski2.spanPrev v i` is the `ℝ`-span of those members of a family
`v : Fin k → (Fin d → ℤ)` of lattice vectors whose index is `< i`.  It is the flag
subspace attached to the greedy construction of the successive minima, and the
index at which the "minimiser outside the previous span" lives.
-/

namespace Work.BW.Minkowski2

/-- The `ℝ`-span of the members of `v : Fin k → (Fin d → ℤ)` with index `< i`. -/
noncomputable def spanPrev {d k : ℕ} (v : Fin k → (Fin d → ℤ)) (i : Fin k) :
    Submodule ℝ (Fin d → ℝ) :=
  Submodule.span ℝ (Set.range (fun j : {j : Fin k // (j : ℕ) < (i : ℕ)} => Work.BW.castVec (v j)))

end Work.BW.Minkowski2
