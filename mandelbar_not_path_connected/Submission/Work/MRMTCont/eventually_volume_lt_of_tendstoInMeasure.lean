import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMTCont

/-- On a finite measure space, a sequence of AEStronglyMeasurable functions that converges
almost everywhere also converges in measure; consequently the (restricted) measure of the
set where a fixed positive threshold is exceeded is eventually small. Transporting back to
`volume` using the fact that the relevant set is contained in `B`. -/
theorem eventually_volume_lt_of_tendstoInMeasure {ν : ℕ → ℕ → ℂ → ℂ} {g : ℕ → ℂ → ℂ} {B : Set ℂ}
    (hB : MeasurableSet B)
    [MeasureTheory.IsFiniteMeasure ((MeasureTheory.volume : MeasureTheory.Measure ℂ).restrict B)]
    (hmem : ∀ j n, MeasureTheory.AEStronglyMeasurable (ν j n)
      ((MeasureTheory.volume : MeasureTheory.Measure ℂ).restrict B))
    (hae : ∀ j, ∀ᶠ z in (MeasureTheory.ae ((MeasureTheory.volume : MeasureTheory.Measure ℂ).restrict B)),
      Filter.Tendsto (fun n => ν j n z) Filter.atTop (nhds (g j z)))
    (hsupp : ∀ j n, Function.support (fun z => ν j n z - g j z) ⊆ B) (j : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (MeasureTheory.volume : MeasureTheory.Measure ℂ) {z : ℂ | 1 / ((j : ℝ) + 1) < ‖ν j n z - g j z‖}
        ≤ (1 / 2 : ENNReal) ^ (j + 1) := by
  -- Convergence a.e. implies convergence in measure, since the restricted measure is finite.
  have hTIM : MeasureTheory.TendstoInMeasure
      ((MeasureTheory.volume : MeasureTheory.Measure ℂ).restrict B)
      (fun n => ν j n) Filter.atTop (g j) :=
    MeasureTheory.tendstoInMeasure_of_tendsto_ae (fun n => hmem j n) (hae j)
  have hr : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
  -- Rewrite convergence in measure in the norm formulation, at threshold `1/(j+1)`.
  have hnorm := (MeasureTheory.tendstoInMeasure_iff_norm.mp hTIM) (1 / ((j : ℝ) + 1)) hr
  have hc : (0 : ENNReal) < (1 / 2 : ENNReal) ^ (j + 1) := ENNReal.pow_pos (by norm_num) _
  -- The measure of `{r ≤ ‖ν - g‖}` is eventually below `(1/2)^(j+1)`.
  filter_upwards [hnorm.eventually (Iio_mem_nhds hc)] with n hn
  -- The set `{r < ‖ν - g‖}` is contained in `B`, since it is contained in the support.
  have hsub : {z : ℂ | 1 / ((j : ℝ) + 1) < ‖ν j n z - g j z‖} ⊆ B := by
    intro z hz
    apply hsupp j n
    rw [Function.mem_support]
    intro h
    change 1 / ((j : ℝ) + 1) < ‖ν j n z - g j z‖ at hz
    rw [h, norm_zero] at hz
    exact absurd hz (not_lt.mpr (le_of_lt hr))
  calc (MeasureTheory.volume : MeasureTheory.Measure ℂ)
        {z : ℂ | 1 / ((j : ℝ) + 1) < ‖ν j n z - g j z‖}
      = (MeasureTheory.volume : MeasureTheory.Measure ℂ)
          ({z : ℂ | 1 / ((j : ℝ) + 1) < ‖ν j n z - g j z‖} ∩ B) := by
        rw [Set.inter_eq_left.mpr hsub]
    _ = ((MeasureTheory.volume : MeasureTheory.Measure ℂ).restrict B)
          {z : ℂ | 1 / ((j : ℝ) + 1) < ‖ν j n z - g j z‖} := by
        rw [MeasureTheory.Measure.restrict_apply' hB]
    _ ≤ ((MeasureTheory.volume : MeasureTheory.Measure ℂ).restrict B)
          {z : ℂ | 1 / ((j : ℝ) + 1) ≤ ‖ν j n z - g j z‖} :=
        MeasureTheory.measure_mono
          (fun z hz => le_of_lt (show 1 / ((j : ℝ) + 1) < ‖ν j n z - g j z‖ from hz))
    _ ≤ (1 / 2 : ENNReal) ^ (j + 1) := le_of_lt hn

end Work.MRMTCont
