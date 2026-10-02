import Mathlib
import Submission.Work.ThomBordism.PosAtlas.chartTrChangeSigned_gen

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `chartTr` agrees for charts related by an orientation-preserving affine transition

If two `ℝⁿ`-charts `e`, `f` of a `T₁` space `W` at a common point `w` satisfy
`f (e.symm z) = A z + b` for all `z` in the target of `e`, with `A` invertible and
`0 < det A`, then the chart transfers of the Euclidean local generator agree:

  `chartTr e w he (eucFam n hn (e w)) = chartTr f w hf (eucFam n hn (f w))`.

Since the transition is *eventually equal* to the affine map `z ↦ A z + b` near `e w`
(the target of `e` is an open neighbourhood of `e w`), it has derivative `A` at `e w`
(`HasFDerivAt.congr_of_eventuallyEq`), so the signed change-of-chart formula
`Work.ThomBordism.PosAtlas.chartTrChangeSigned_gen` applies with sign `+1`.
-/

namespace Work.ThomBordism.PosAtlas

theorem chartTr_eq_of_affine_transition {n : ℕ} (hn : 1 ≤ n) {W : TopCat} [T1Space W]
    (e f : OpenPartialHomeomorph W (EuclideanSpace ℝ (Fin n)))
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : Function.Bijective A) (b : EuclideanSpace ℝ (Fin n))
    (htrans : ∀ z ∈ e.target, f (e.symm z) = A z + b)
    (hdet : 0 < LinearMap.det A.toLinearMap)
    (w : W) (he : w ∈ e.source) (hf : w ∈ f.source) :
    Work.PTGeometric.HOF.chartTr e w he (Work.PTGeometric.HOF.eucFam n hn (e w))
      = Work.PTGeometric.HOF.chartTr f w hf (Work.PTGeometric.HOF.eucFam n hn (f w)) := by
  -- the derivative of the transition is `A`, since the transition agrees with `z ↦ A z + b`
  -- on a neighbourhood of `e w`
  have hd : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) => f (e.symm z)) A (e w) := by
    have haff : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) => A z + b) A (e w) :=
      (A.hasFDerivAt).add_const b
    refine haff.congr_of_eventuallyEq ?_
    exact Filter.eventually_of_mem (e.open_target.mem_nhds (e.map_source he)) htrans
  have h := chartTrChangeSigned_gen n hn e f w he hf A hA hd
  rwa [if_pos hdet, one_smul] at h

end Work.ThomBordism.PosAtlas
