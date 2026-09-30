import Mathlib
import Submission.Work.BW.DefsB

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-! Definitions for the partial-degeneracy reduction in `multiplicity_prop` (install next to
`DefsMult` as `Submission/Work/BW/DefsMP.lean`, namespace `Work.BW`). `σ : Fin N' → Fin r`
enumerates (increasingly) the torus coordinates `i` with `𝒟 (i.succ) ≥ 1`. -/

/-- Index map `Fin (N'+1) → Fin (r+1)`: `0 ↦ 0`, `j.succ ↦ (σ j).succ`. -/
def liftIdx {N' r : ℕ} (σ : Fin N' → Fin r) : Fin (N' + 1) → Fin (r + 1) :=
  fun i => Fin.cases (motive := fun _ => Fin (r + 1)) 0 (fun j => (σ j).succ) i

/-- Extension by zero of a lattice basis on the coordinates `range σ` to all of `Fin r`. -/
noncomputable def extM {N' r ρ : ℕ} (σ : Fin N' → Fin r) (M' : Fin ρ → Fin N' → ℤ) :
    Fin ρ → Fin r → ℤ :=
  fun j => Function.extend σ (M' j) 0

end Work.BW
