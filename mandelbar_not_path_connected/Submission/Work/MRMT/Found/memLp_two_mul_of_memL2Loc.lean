import Mathlib
import Submission.Work.MRMT.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

open MeasureTheory

/-- If `μ` is essentially bounded (by `k`) and supported in the closed ball of radius `R`,
then `μ · D` is globally `L²` for any locally `L²` function `D`. -/
theorem memLp_two_mul_of_memL2Loc {μ D : ℂ → ℂ} {R k : ℝ}
    (hmeas : MeasureTheory.AEStronglyMeasurable (fun z => μ z * D z)
      (MeasureTheory.volume : MeasureTheory.Measure ℂ))
    (hD : Work.MRMT.MemL2Loc D)
    (hb : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), ‖μ z‖ ≤ k)
    (hsupp : Function.support μ ⊆ Metric.closedBall 0 R) :
    MeasureTheory.MemLp (fun z => μ z * D z) 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ) := by
  set K : Set ℂ := Metric.closedBall (0:ℂ) R with hKdef
  have hKc : IsCompact K := isCompact_closedBall (0:ℂ) R
  have hKmeas : MeasurableSet K := hKc.isClosed.measurableSet
  have hDint : IntegrableOn (fun z => ‖D z‖ ^ 2) K volume := by
    have := hD K hKc
    simpa [Work.MRMT.MemL2Loc, Work.MRMT.MemL2LocOn] using this
  have hbndint : Integrable (K.indicator (fun z => (max k 0)^2 * ‖D z‖ ^ 2)) volume := by
    rw [integrable_indicator_iff hKmeas]
    exact hDint.const_mul _
  have hle : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), ‖‖μ z * D z‖ ^ 2‖ ≤
      K.indicator (fun z => (max k 0)^2 * ‖D z‖ ^ 2) z := by
    filter_upwards [hb] with z hz
    by_cases hzk : z ∈ K
    · rw [Set.indicator_of_mem hzk]
      have h0 : (0:ℝ) ≤ max k 0 := le_max_right _ _
      have h1 : ‖μ z‖ ≤ max k 0 := le_trans hz (le_max_left _ _)
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      calc ‖μ z * D z‖ ^ 2 = (‖μ z‖ * ‖D z‖) ^ 2 := by rw [norm_mul]
        _ ≤ ((max k 0) * ‖D z‖) ^ 2 := by
              exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)) 2
        _ = (max k 0)^2 * ‖D z‖ ^ 2 := by ring
    · rw [Set.indicator_of_notMem hzk]
      have hz0 : μ z = 0 := by
        by_contra hcon
        exact hzk (hsupp hcon)
      simp [hz0]
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  exact Integrable.mono' hbndint (hmeas.norm.pow 2) hle

end Work.MRMT.Found
