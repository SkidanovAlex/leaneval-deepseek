import Mathlib
import Submission.Work.FatouCoordFix.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouCoordFix.HPetal

open Set

/-- The half-plane `{W : ℂ | M < W.re}` is convex, hence preconnected. -/
theorem convex_re_gt (M : ℝ) : Convex ℝ {W : ℂ | M < W.re} := by
  have h : {W : ℂ | M < W.re} = Complex.reLm ⁻¹' (Set.Ioi M) := rfl
  rw [h]
  exact (convex_Ioi M).linear_preimage Complex.reLm

/-- For `M ≥ 0` the half-plane `{W : ℂ | M < W.re}` avoids `0`, so the parabolic chart
`W ↦ -1 / W` is continuous on it. -/
theorem continuousOn_neg_one_div {M : ℝ} (hM : 0 ≤ M) :
    ContinuousOn (fun W : ℂ => -1 / W) {W : ℂ | M < W.re} := by
  refine ContinuousOn.div continuousOn_const continuousOn_id ?_
  intro W hW h0
  rw [h0] at hW
  simp at hW
  linarith

/-- The half-plane petal `HPlanePetal M` is the image of the half-plane `{Re W > M}` under the
parabolic chart `W ↦ -1/W`, therefore preconnected. -/
theorem HPlanePetal_preconnected {M : ℝ} (hM : 0 ≤ M) : IsPreconnected (Work.FatouCoordFix.HPlanePetal M) := by
  rw [Work.FatouCoordFix.HPlanePetal_eq_image hM]
  refine IsPreconnected.image ?_ (fun W : ℂ => -1 / W) ?_
  · exact (convex_re_gt M).isPreconnected
  · exact continuousOn_neg_one_div hM

end Work.FatouCoordFix.HPetal
