import Mathlib
import Submission.Work.FatouCoordFix.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouCoordFix.HPetal

/-- In the parabolic chart `W = -1/u`, membership of `u` in `HPlanePetal M` says `M < W.re`, and
`-1/(g u) = gChart g W`.  So a growth bound `Re (gChart g W) ≥ M + 1/4` on the half-plane
`{M < Re W}` turns `HPlanePetal M` into a `g`-invariant set — provided `M ≥ 0`, which is what
rules out the degenerate case `g u = 0` (there `-1/(g u) = 0` and the growth bound would force
`M + 1/4 ≤ 0`). -/
theorem HPlanePetal_mapsTo_gChart {g : ℂ → ℂ} {M : ℝ} (hM : 0 ≤ M) (hgr : ∀ W : ℂ, M < W.re → M + 1 / 4 ≤ (Work.FatouCoord.Flower.gChart g W).re) : Set.MapsTo g (Work.FatouCoordFix.HPlanePetal M) (Work.FatouCoordFix.HPlanePetal M) := by
  intro u hu
  obtain ⟨hu0, huM⟩ := hu
  -- `u ∈ HPlanePetal M` gives `M < W.re` for the chart value `W = -1/u`
  have hgrW := hgr (-1 / u) huM
  -- the chart value of `-1/(g u)` is `gChart g (-1/u)`
  have hchart : Work.FatouCoord.Flower.gChart g (-1 / u) = -1 / g u := by
    rw [Work.FatouCoord.Flower.mem_gChart, Work.FatouCoordFix.neg_one_div_neg_one_div' hu0]
  have hmem : M < (-1 / (g u)).re := by
    rw [← hchart]
    linarith
  -- `g u ≠ 0`: otherwise `-1/(g u) = 0` and `hmem` would give `M < 0 ≤ M`
  have hgu0 : g u ≠ 0 := by
    intro h0
    rw [h0] at hmem
    simp at hmem
    linarith
  exact ⟨hgu0, hmem⟩

end Work.FatouCoordFix.HPetal
