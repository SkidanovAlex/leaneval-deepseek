import Mathlib.Analysis.SpecialFunctions.NonIntegrable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

/-- If `F ≥ 0` on `(0, ∞)`, `F z / z` is integrable on `(0, ∞)` and `F` has a limit `L`
at `0⁺`, then `L ≤ 0`.

Indeed, if `L > 0` then `F z ≥ L/2` for all small `z > 0`, whence
`(F z) / z ≥ (L/2) / z` on a small interval `(0, δ)`; integrability of `F z / z` there
would force `z ↦ z⁻¹` to be integrable on `(0, δ)`, contradicting
`intervalIntegrable_inv_iff`. -/
theorem le_zero_of_tendsto_nhdsGT_zero_of_integrableOn_div {F : ℝ → ℝ} {L : ℝ}
    (hpos : ∀ z ∈ Set.Ioi (0 : ℝ), 0 ≤ F z)
    (hint : MeasureTheory.IntegrableOn (fun z => F z / z) (Set.Ioi 0))
    (hL : Filter.Tendsto F (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds L)) : L ≤ 0 := by
  -- `hpos` is not needed: the lower bound on `F` near `0⁺` comes from the limit `hL`.
  have hFnn : ∀ z ∈ Set.Ioi (0 : ℝ), 0 ≤ F z := hpos
  by_contra h
  push Not at h
  set m : ℝ := L / 2 with hm
  have hmpos : 0 < m := by rw [hm]; linarith
  have hmL : m < L := by rw [hm]; linarith
  -- `F z > m` for all `z` close enough to `0` on the right
  have hmm : ∀ᶠ z in nhdsWithin (0 : ℝ) (Set.Ioi 0), m < F z :=
    hL.eventually (Ioi_mem_nhds hmL)
  rw [eventually_nhdsWithin_iff] at hmm
  rw [Metric.eventually_nhds_iff] at hmm
  obtain ⟨ε, hε, hε'⟩ := hmm
  set δ : ℝ := ε / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  -- integrability transfers to the small interval `(0, δ)`
  have hIoc : MeasureTheory.IntegrableOn (fun z => F z / z) (Set.Ioc 0 δ) :=
    hint.mono_set (fun z hz => hz.1)
  have hgint : MeasureTheory.Integrable (fun z => (F z / z) / m)
      (MeasureTheory.volume.restrict (Set.Ioc 0 δ)) :=
    hIoc.div_const m
  have haesm : MeasureTheory.AEStronglyMeasurable (fun z : ℝ => z⁻¹)
      (MeasureTheory.volume.restrict (Set.Ioc 0 δ)) :=
    (measurable_inv (G := ℝ)).aestronglyMeasurable
  -- on `(0, δ)` the function `z ↦ z⁻¹` is dominated by `z ↦ (F z / z) / m`
  have hae : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioc 0 δ)),
      ‖(z : ℝ)⁻¹‖ ≤ (F z / z) / m := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with z hz
    have hzpos : 0 < z := hz.1
    have hdist : dist z 0 < ε := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hzpos]
      linarith [hz.2]
    have hF : m < F z := hε' hdist hz.1
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hzpos)]
    rw [le_div_iff₀ hmpos, inv_mul_eq_div]
    exact div_le_div_of_nonneg_right hF.le hzpos.le
  have hzint : MeasureTheory.Integrable (fun z : ℝ => z⁻¹)
      (MeasureTheory.volume.restrict (Set.Ioc 0 δ)) :=
    MeasureTheory.Integrable.mono' hgint haesm hae
  -- but `z ↦ z⁻¹` is not integrable on `(0, δ)`
  have hnot : ¬ IntervalIntegrable (fun z : ℝ => z⁻¹) MeasureTheory.volume 0 δ := by
    intro hII
    have h₁ : (0 : ℝ) = δ ∨ 0 ∉ Set.uIcc (0 : ℝ) δ := intervalIntegrable_inv_iff.mp hII
    rcases h₁ with h₁ | h₁
    · exact absurd h₁ (ne_of_lt hδ)
    · exact h₁ (by rw [Set.uIcc_of_le hδ.le]; exact ⟨le_refl 0, hδ.le⟩)
  exact hnot (by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hδ.le]
    exact hzint)

end Work.FTS.EllipticEst
