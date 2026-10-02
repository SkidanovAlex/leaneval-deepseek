import Mathlib
import Submission.Work.MRMT.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

open MeasureTheory ENNReal

/-- A complex-valued function which is essentially bounded by a real constant `C` and whose
support is contained in a closed ball is square integrable: the a.e. bound can be replaced by
`max C 0 ≥ 0` and the closed ball has finite volume, so the squared modulus is dominated a.e. by
a constant on a finite-measure set. -/
theorem memLp_two_of_ae_bound_of_support {f : ℂ → ℂ} {C S : ℝ}
    (hmeas : MeasureTheory.AEStronglyMeasurable f (MeasureTheory.volume : MeasureTheory.Measure ℂ))
    (hb : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), ‖f z‖ ≤ C)
    (hs : Function.support f ⊆ Metric.closedBall (0 : ℂ) S) :
    MeasureTheory.MemLp f 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ) := by
  set K : Set ℂ := Metric.closedBall (0 : ℂ) S with hKdef
  have hKc : IsCompact K := isCompact_closedBall (0 : ℂ) S
  have hKmeas : MeasurableSet K := hKc.isClosed.measurableSet
  set c : ℝ := max C 0 with hcdef
  have hb' : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), ‖f z‖ ≤ c :=
    hb.mono fun z hz => le_trans hz (le_max_left _ _)
  have hKtop : (MeasureTheory.volume : MeasureTheory.Measure ℂ) K ≠ ⊤ :=
    ne_of_lt hKc.measure_lt_top
  have hKint : Integrable (K.indicator (fun _ : ℂ => c ^ 2))
      (MeasureTheory.volume : MeasureTheory.Measure ℂ) := by
    rw [integrable_indicator_iff hKmeas]
    exact integrableOn_const hKtop (ne_of_lt enorm_lt_top)
  have hle : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
      ‖‖f z‖ ^ 2‖ ≤ K.indicator (fun _ : ℂ => c ^ 2) z := by
    filter_upwards [hb'] with z hz
    by_cases hzk : z ∈ K
    · rw [Set.indicator_of_mem hzk, Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) hz 2
    · rw [Set.indicator_of_notMem hzk]
      have hz0 : f z = 0 := by
        by_contra hcon
        exact hzk (hs hcon)
      simp [hz0]
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  exact Integrable.mono' hKint (hmeas.norm.pow 2) hle

end Work.MRMT.Found
