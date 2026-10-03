import Mathlib
import Submission.Work.OROneRel.tlWindowHalvesDefs
import Submission.Work.OROneRel.bandLoopsDefs
import Submission.Work.OROneRel.mem_winRho_range_iff
import Submission.Work.OROneRel.twoLetter_generation

/-!
# The gauge-free window subgroups `bandWin`

`bandWin p q m` is the `π₁` of the window `[0,m]` of the `tlW p q`-level graph `Y`: the subgroup of
`F₂` of the elements whose *reduced* word walks inside `winE (tlW p q) 0 m` (`loopsInE`,
`bandLoopsDefs.lean`).  It is the gauge-free object used by the climb for the two-letter band; at
`m = p*q` it is the band vertex `tlH p q Wt` (`Work.OROneRel.tlH_eq_loopsInE`), and the window
recursion `bandWin (m+1) = bandWin m ⊔ τ (bandWin m) τ⁻¹` holds for `m ≥ p+q-1` (van Kampen for
`[0,m+1] = [0,m] ∪ [1,m+1]`).
-/
namespace Work.OROneRel

/-- **The gauge-free window subgroup** `π₁(Y[0,m])`: the loops of the window `[0,m]`. -/
noncomputable def bandWin (p q : ℕ) (m : ℤ) : Subgroup (FreeGroup (Fin 2)) :=
  loopsInE (tlW p q) (winE (tlW p q) 0 m)

end Work.OROneRel
