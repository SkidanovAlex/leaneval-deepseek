import Mathlib
import Submission.Work.FatouCoordFix.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The attracting petal `Petal r M` sits inside the wide petal `WidePetal M`

The *petal* `Work.FatouCoord.Petal r M = {z | ‖z‖ < r ∧ z.re < -M * normSq z}` is, in the
parabolic chart `W = -1/z`, the right half-plane condition `M < Re W`: indeed
`Re (-1 / z) = -z.re / normSq z`, so `z.re < -M * normSq z` unfolds to `Re (-1 / z) > M`.

The *wide petal* `Work.FatouCoord.Flower.WidePetal M = {u | u ≠ 0 ∧ M < sgauge (-1 / u)}`
uses the gauge `sgauge W = W.re + |W.im| ≥ W.re` of the sector of opening `3π/2`.  Since
`sgauge ≥ Re`, the petal — a sector of opening `π` — is contained in the wide petal.  The
hypothesis `0 ≤ M` is not needed for the inclusion; it records that the wide petal is the
relevant object when `M` is a positive level.
-/

set_option linter.unusedVariables false

namespace Work.FatouCoordFix.HPetal

theorem Petal_subset_WidePetal {r M : ℝ} (hM : 0 ≤ M) : Work.FatouCoord.Petal r M ⊆ Work.FatouCoord.Flower.WidePetal M := by
  intro z hz
  obtain ⟨hr, hlt⟩ := hz
  -- `z.re < -M * normSq z` already forces `z ≠ 0`
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hlt
    simp at hlt
  refine ⟨hz0, ?_⟩
  rw [Work.FatouCoord.Flower.mem_sgauge]
  have hns : (0 : ℝ) < Complex.normSq z := Complex.normSq_pos.mpr hz0
  -- the real and imaginary parts of the chart coordinate `-1 / z`
  have hkey : (-1 / z).re = -z.re / Complex.normSq z := by
    rw [Complex.div_re]; simp
  have hkey2 : (-1 / z).im = z.im / Complex.normSq z := by
    rw [Complex.div_im]; simp; ring
  rw [hkey, hkey2]
  -- the petal hypothesis is exactly `M < Re (-1 / z)`
  have h1 : M < -z.re / Complex.normSq z := by
    rw [lt_div_iff₀ hns]
    linarith
  have h2 : 0 ≤ |z.im / Complex.normSq z| := abs_nonneg _
  linarith

end Work.FatouCoordFix.HPetal
