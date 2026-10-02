import Mathlib
import Submission.Work.FatouParabolic.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouParabolic.Basin

open Filter
open scoped Topology

set_option linter.unusedVariables false in
theorem mapsTo_puncturedBasin {f : ℂ → ℂ} {z₀ z : ℂ} (hfix : f z₀ = z₀)
    (hz : z ∈ Work.FatouParabolic.puncturedBasin f z₀) :
    f z ∈ Work.FatouParabolic.puncturedBasin f z₀ := by
  simp only [Work.FatouParabolic.mem_puncturedBasin, Work.FatouParabolic.mem_basin] at hz ⊢
  obtain ⟨hne, hconv⟩ := hz
  refine ⟨?_, ?_⟩
  · intro n
    rw [← Function.iterate_succ_apply f n z]
    exact hne (n + 1)
  · rw [show (fun n : ℕ => f^[n] (f z)) = (fun n : ℕ => f^[n + 1] z) from
      funext fun n => (Function.iterate_succ_apply f n z).symm]
    exact (Filter.tendsto_add_atTop_iff_nat (f := fun n => f^[n] z) 1).mpr hconv

end Work.FatouParabolic.Basin
