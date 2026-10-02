import Mathlib
import Submission.Work.ParamRays.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ParamRays

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- Continuity of `z ↦ T_c^[n] z`, the orbit map. -/
theorem continuous_orbit (c : ℂ) (n : ℕ) : Continuous fun z : ℂ => orbit c z n := by
  have hcont : Continuous (Tantibar c) := by
    unfold Tantibar
    exact ((Complex.continuous_conj.pow 2)).add continuous_const
  exact show Continuous ((Tantibar c)^[n]) from hcont.iterate n

/-- The filled Julia set as an intersection of closed "escape radius" conditions. -/
theorem filledJulia_eq_iInter (c : ℂ) :
    Work.ParamRays.filledJulia c = ⋂ n : ℕ, {z : ℂ | ‖orbit c z n‖ ≤ max 2 ‖c‖} := by
  ext z
  simp only [Set.mem_iInter, Set.mem_ofPred_eq, filledJulia, BoundedOrbit]
  exact ⟨fun h n => norm_le_max_of_bounded c (orbit c z n) (BoundedOrbit.shift h n),
         fun h => ⟨max 2 ‖c‖, h⟩⟩

/-- The filled Julia set of `T_c` is closed.

Indeed `filledJulia c = ⋂ n, {z | ‖orbit c z n‖ ≤ max 2 ‖c‖}`: one inclusion is
`norm_le_max_of_bounded` applied along the orbit (`BoundedOrbit.shift`), the other is immediate
from `BoundedOrbit`; each set in the intersection is closed because `z ↦ orbit c z n` is
continuous (an iterate of the continuous map `Tantibar c`). -/
theorem isClosed_filledJulia (c : ℂ) : IsClosed (Work.ParamRays.filledJulia c) := by
  rw [filledJulia_eq_iInter]
  exact isClosed_iInter fun n => isClosed_le (continuous_orbit c n).norm continuous_const

end Work.ParamRays
