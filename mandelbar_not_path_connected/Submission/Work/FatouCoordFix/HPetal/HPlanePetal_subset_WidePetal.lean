import Mathlib
import Submission.Work.FatouCoordFix.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouCoordFix.HPetal

/-- The half-plane petal `{u ≠ 0 | M < Re (-1/u)}` is contained in the wide petal of any lower
level `M' ≤ M`: the wide gauge `sgauge W = Re W + |Im W|` dominates `Re W`, so `M < Re W` forces
`M' < sgauge W`. -/
theorem HPlanePetal_subset_WidePetal {M M' : ℝ} (h : M' ≤ M) :
    Work.FatouCoordFix.HPlanePetal M ⊆ Work.FatouCoord.Flower.WidePetal M' := by
  intro u hu
  rw [Work.FatouCoordFix.mem_HPlanePetal] at hu
  rw [Work.FatouCoord.Flower.mem_WidePetal]
  obtain ⟨hu0, huM⟩ := hu
  refine ⟨hu0, ?_⟩
  have hle : (-1 / u).re ≤ Work.FatouCoord.Flower.sgauge (-1 / u) := by
    rw [Work.FatouCoord.Flower.sgauge]
    exact le_add_of_nonneg_right (abs_nonneg _)
  linarith

end Work.FatouCoordFix.HPetal
