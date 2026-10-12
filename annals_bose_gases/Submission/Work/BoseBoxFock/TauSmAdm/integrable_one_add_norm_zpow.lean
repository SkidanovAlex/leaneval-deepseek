import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseBoxFock/TauSmAdm/integrable_one_add_norm_zpow.lean`

**`integrable_one_add_norm_zpow`.**  The radial weight `p ↦ (1 + ‖p‖) ^ (-(5 : ℤ))` is
integrable on `ℝ³` with respect to Lebesgue measure.

This is the integer-exponent form of Mathlib's `integrable_one_add_norm`, which gives
integrability of `x ↦ (1 + ‖x‖) ^ (-r)` (with `r : ℝ`) for `r > finrank ℝ E`.  The two are
related pointwise by `Real.rpow_neg_natCast`, `x ^ (-n : ℝ) = x ^ (-n : ℤ)`, and on
`EuclideanSpace ℝ (Fin 3)` the finrank is `3 < 5`.
-/

noncomputable section

namespace Work.BoseBoxFock.TauSmAdm

open MeasureTheory Module

theorem integrable_one_add_norm_zpow :
    MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => (1 + ‖p‖) ^ (-(5 : ℤ))) volume := by
  have hfin : (finrank ℝ (EuclideanSpace ℝ (Fin 3)) : ℝ) < 5 := by
    rw [finrank_euclideanSpace_fin]; norm_num
  refine (integrable_one_add_norm (E := EuclideanSpace ℝ (Fin 3)) (μ := volume)
    (r := 5) hfin).congr ?_
  filter_upwards with p
  simp

end Work.BoseBoxFock.TauSmAdm
