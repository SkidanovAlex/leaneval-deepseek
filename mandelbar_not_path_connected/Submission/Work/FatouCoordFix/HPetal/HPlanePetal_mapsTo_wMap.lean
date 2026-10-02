import Mathlib
import Submission.Work.FatouCoordFix.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouCoordFix.HPetal

/-- **`f` preserves the half-plane petal `HPlanePetal M`.**

The half-plane petal `HPlanePetal M = {u ≠ 0 | M < Re (-1/u)}` is the image of the half-plane
`{Re W > M}` of the parabolic chart `W = -1/u` under `W ↦ -1/W`.  A point `u` of the petal has
chart value `W = -1/u`, whose `f`-image in the chart is `wMap f W = chart (f (chart W))`.  On the
half-plane `Re W > M ≥ 0` the hypothesis `hgr` keeps the real part above `M`; since `u ≠ 0`
gives `chart W = u`, this says exactly that `chart (f u) = -1/(f u)` has real part `> M ≥ 0`,
which in particular forces `f u ≠ 0` (if `f u = 0` then `-1/(f u) = 0`, so `M < 0`, absurd). -/
theorem HPlanePetal_mapsTo_wMap {f : ℂ → ℂ} {M : ℝ} (hM : 0 ≤ M) (hgr : ∀ W : ℂ, M < W.re → M < (Work.FatouCoord.wMap f W).re) : Set.MapsTo f (Work.FatouCoordFix.HPlanePetal M) (Work.FatouCoordFix.HPlanePetal M) := by
  intro u hu
  obtain ⟨hu0, huM⟩ := hu
  -- In the chart, `u` has value `W = -1/u`, and `chart W = u` because `u ≠ 0`.
  have hwmap : Work.FatouCoord.wMap f (-1 / u) = -1 / (f u) := by
    rw [Work.FatouCoord.wMap_apply, neg_one_div_neg_one_div' hu0]
  have hre : M < (-1 / (f u)).re := by
    have := hgr (-1 / u) huM
    rwa [hwmap] at this
  refine ⟨?_, hre⟩
  -- If `f u = 0` then `-1/(f u) = 0`, contradicting `M < 0 ≤ M`.
  intro hf
  rw [hf] at hre
  simp at hre
  linarith

end Work.FatouCoordFix.HPetal
