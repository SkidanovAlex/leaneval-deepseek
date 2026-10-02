import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.unusedVariables false

namespace Work.MRMT.Found

open MeasureTheory Filter
open scoped ENNReal Topology

/-- Elementary truncation inequality: for `M > 0` the "tail" `r - min r M` is at most `r²/M`. -/
private lemma sub_min_le_sq_div (r M : ℝ) (hM : 0 < M) : r - min r M ≤ r ^ 2 / M := by
  rcases le_total r M with h | h
  · rw [min_eq_left h, sub_self]
    exact div_nonneg (sq_nonneg r) hM.le
  · rw [min_eq_right h, le_div_iff₀ hM]
    nlinarith [sq_nonneg (r - M / 2), sq_nonneg M]

/-- Splitting `C*s*r` into its "small" and "tail" parts with respect to the threshold `M`. -/
private lemma ofReal_mul_min_decomp {C M s r : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M) (hs : 0 ≤ s)
    (hr : 0 ≤ r) :
    ENNReal.ofReal (C * s * r)
      = ENNReal.ofReal (C * s * min r M) + ENNReal.ofReal (C * s * (r - min r M)) := by
  rw [← ENNReal.ofReal_add]
  · congr 1
    ring_nf
  · exact mul_nonneg (mul_nonneg hC hs) (le_min hr hM)
  · exact mul_nonneg (mul_nonneg hC hs) (sub_nonneg.mpr (min_le_left _ _))

theorem tendsto_lintegral_ofReal_mul_of_ae_tendsto_zero {Ω : Set ℂ} (hΩ : MeasurableSet Ω)
    (hΩfin : MeasureTheory.volume Ω ≠ ⊤) {C : ℝ} (hC : 0 ≤ C)
    {ν : ℕ → ℂ → ℂ} (hνmeas : ∀ n, MeasureTheory.AEStronglyMeasurable (ν n) MeasureTheory.volume)
    {b : ℕ → ℂ → ℂ} (hbmeas : ∀ n, MeasureTheory.AEStronglyMeasurable (b n) MeasureTheory.volume)
    (hν0 : Filter.Eventually (fun z => Filter.Tendsto (fun n => ν n z) Filter.atTop (nhds 0))
      (MeasureTheory.ae (MeasureTheory.volume : MeasureTheory.Measure ℂ)))
    (hνb : ∀ n, Filter.Eventually (fun z => ‖ν n z‖ ≤ 2)
      (MeasureTheory.ae (MeasureTheory.volume : MeasureTheory.Measure ℂ)))
    (hbbnd : ∃ B : ℝ, 0 ≤ B ∧ ∀ n,
      MeasureTheory.lintegral (MeasureTheory.Measure.restrict MeasureTheory.volume Ω)
        (fun z => ENNReal.ofReal (‖b n z‖ ^ 2)) ≤ ENNReal.ofReal (B ^ 2)) :
    Filter.Tendsto (fun n => MeasureTheory.lintegral (MeasureTheory.Measure.restrict MeasureTheory.volume Ω)
        (fun z => ENNReal.ofReal (C * ‖ν n z‖ * ‖b n z‖))) Filter.atTop (nhds 0) := by
  set μ : MeasureTheory.Measure ℂ := MeasureTheory.Measure.restrict MeasureTheory.volume Ω with hμdef
  have hμuniv : μ Set.univ = MeasureTheory.volume Ω := by
    rw [hμdef, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  have hνμ : ∀ n, MeasureTheory.AEStronglyMeasurable (ν n) μ := fun n =>
    (hνmeas n).mono_measure (by rw [hμdef]; exact Measure.restrict_le_self)
  have hbμ : ∀ n, MeasureTheory.AEStronglyMeasurable (b n) μ := fun n =>
    (hbmeas n).mono_measure (by rw [hμdef]; exact Measure.restrict_le_self)
  have hνb_μ : ∀ n, ∀ᵐ z ∂μ, ‖ν n z‖ ≤ 2 := fun n =>
    MeasureTheory.ae_restrict_of_ae (μ := MeasureTheory.volume) (s := Ω) (hνb n)
  have hν0_μ : ∀ᵐ z ∂μ, Tendsto (fun n => ν n z) atTop (𝓝 0) :=
    MeasureTheory.ae_restrict_of_ae (μ := MeasureTheory.volume) (s := Ω) hν0
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  by_cases htop : ε = ⊤
  · rw [htop]
    exact Filter.Eventually.of_forall (fun n => le_top)
  obtain ⟨B, hB0, hB⟩ := hbbnd
  have hε0 : ε ≠ 0 := hε.ne'
  have hhalf0 : ε / 2 ≠ 0 := ENNReal.div_ne_zero.mpr ⟨hε0, by norm_num⟩
  have hhalftop : ε / 2 ≠ ⊤ := ENNReal.div_ne_top htop (by norm_num)
  have hepos : 0 < (ε / 2).toReal := ENNReal.toReal_pos hhalf0 hhalftop
  set K : ℝ := 2 * C * B ^ 2 with hKdef
  set M : ℝ := K / (ε / 2).toReal + 1 with hMdef
  have hMpos : 0 < M := by rw [hMdef]; positivity
  have hMbound : ENNReal.ofReal (K / M) ≤ ε / 2 := by
    have hKM : K / M ≤ (ε / 2).toReal := by
      rw [hMdef, div_le_iff₀ (by positivity : (0:ℝ) < K / (ε / 2).toReal + 1)]
      have hcancel : (ε / 2).toReal * (K / (ε / 2).toReal) = K :=
        mul_div_cancel₀ K (ne_of_gt hepos)
      nlinarith [hepos.le, hcancel]
    calc ENNReal.ofReal (K / M) ≤ ENNReal.ofReal ((ε / 2).toReal) := ENNReal.ofReal_le_ofReal hKM
      _ ≤ ε / 2 := ENNReal.ofReal_toReal_le
  -- measurability of the "small" integrand
  have hGmeas : ∀ n, AEMeasurable
      (fun z => ENNReal.ofReal (C * ‖ν n z‖ * min (‖b n z‖) M)) μ := by
    intro n
    have hνR : AEMeasurable (fun z => ‖ν n z‖) μ := (hνμ n).aemeasurable.norm
    have hbR : AEMeasurable (fun z => ‖b n z‖) μ := (hbμ n).aemeasurable.norm
    have hreal : AEMeasurable (fun z => C * ‖ν n z‖ * min (‖b n z‖) M) μ :=
      (hνR.const_mul C).mul (hbR.min aemeasurable_const)
    exact ENNReal.measurable_ofReal.comp_aemeasurable hreal
  -- the "small" part tends to zero by dominated convergence
  have hA : Tendsto (fun n => ∫⁻ z,
      ENNReal.ofReal (C * ‖ν n z‖ * min (‖b n z‖) M) ∂μ) atTop (𝓝 0) := by
    have hbnd : ∀ n, (fun z => ENNReal.ofReal (C * ‖ν n z‖ * min (‖b n z‖) M))
        ≤ᵐ[μ] (fun _ => ENNReal.ofReal (2 * C * M)) := by
      intro n
      filter_upwards [hνb_μ n] with z hz
      apply ENNReal.ofReal_le_ofReal
      have h1 : C * ‖ν n z‖ ≤ C * 2 := mul_le_mul_of_nonneg_left hz hC
      have h2 : min (‖b n z‖) M ≤ M := min_le_right _ _
      have h3 : 0 ≤ min (‖b n z‖) M := le_min (norm_nonneg _) hMpos.le
      have h4 : 0 ≤ C * 2 := by positivity
      calc C * ‖ν n z‖ * min (‖b n z‖) M ≤ (C * 2) * M := mul_le_mul h1 h2 h3 h4
        _ = 2 * C * M := by ring
    have hfin : ∫⁻ z, (fun _ => ENNReal.ofReal (2 * C * M)) z ∂μ ≠ ⊤ := by
      rw [lintegral_const, hμuniv]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hΩfin
    have hlim : ∀ᵐ z ∂μ, Tendsto (fun n =>
        ENNReal.ofReal (C * ‖ν n z‖ * min (‖b n z‖) M)) atTop (𝓝 (0:ℝ≥0∞)) := by
      filter_upwards [hν0_μ] with z hz
      have hzr : Tendsto (fun n => ‖ν n z‖) atTop (𝓝 0) := by
        simpa using hz.norm
      have hreal : Tendsto (fun n => C * ‖ν n z‖ * min (‖b n z‖) M) atTop (𝓝 0) := by
        have h1 : Tendsto (fun n => ‖ν n z‖ * (C * M)) atTop (𝓝 0) := by
          simpa using hzr.mul_const (C * M)
        refine squeeze_zero (f := fun n => C * ‖ν n z‖ * min (‖b n z‖) M)
          (g := fun n => ‖ν n z‖ * (C * M)) (fun n => ?_) (fun n => ?_) ?_
        · exact mul_nonneg (mul_nonneg hC (norm_nonneg _)) (le_min (norm_nonneg _) hMpos.le)
        · have hmin : min (‖b n z‖) M ≤ M := min_le_right _ _
          rw [show C * ‖ν n z‖ * min (‖b n z‖) M
                = ‖ν n z‖ * (C * min (‖b n z‖) M) by ring]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmin hC) (norm_nonneg _)
        · simpa using h1
      have := (ENNReal.continuous_ofReal.tendsto 0).comp hreal
      simpa [Function.comp_def] using this
    have h := tendsto_lintegral_of_dominated_convergence' (μ := μ)
      (F := fun n z => ENNReal.ofReal (C * ‖ν n z‖ * min (‖b n z‖) M))
      (f := fun _ => (0:ℝ≥0∞)) (fun _ => ENNReal.ofReal (2 * C * M))
      (fun n => hGmeas n) hbnd hfin hlim
    simpa using h
  -- the "tail" part is uniformly bounded by `ε / 2`
  have hHbound : ∀ n, ∫⁻ z, ENNReal.ofReal
      (C * ‖ν n z‖ * (‖b n z‖ - min (‖b n z‖) M)) ∂μ ≤ ε / 2 := by
    intro n
    have hpt : ∀ᵐ z ∂μ, ENNReal.ofReal (C * ‖ν n z‖ * (‖b n z‖ - min (‖b n z‖) M))
        ≤ ENNReal.ofReal ((2 * C / M) * ‖b n z‖ ^ 2) := by
      filter_upwards [hνb_μ n] with z hz
      apply ENNReal.ofReal_le_ofReal
      have htail : 0 ≤ ‖b n z‖ - min (‖b n z‖) M := sub_nonneg.mpr (min_le_left _ _)
      have h1 : ‖b n z‖ - min (‖b n z‖) M ≤ ‖b n z‖ ^ 2 / M := sub_min_le_sq_div _ _ hMpos
      have h2 : C * ‖ν n z‖ ≤ C * 2 := mul_le_mul_of_nonneg_left hz hC
      calc C * ‖ν n z‖ * (‖b n z‖ - min (‖b n z‖) M)
          ≤ (C * 2) * (‖b n z‖ ^ 2 / M) :=
            mul_le_mul h2 h1 htail (by positivity)
        _ = (2 * C / M) * ‖b n z‖ ^ 2 := by ring
    have hconst_meas : AEMeasurable (fun z => ENNReal.ofReal (‖b n z‖ ^ 2)) μ := by
      have hbR : AEMeasurable (fun z => ‖b n z‖) μ := (hbμ n).aemeasurable.norm
      exact ENNReal.measurable_ofReal.comp_aemeasurable (hbR.pow_const 2)
    calc ∫⁻ z, ENNReal.ofReal (C * ‖ν n z‖ * (‖b n z‖ - min (‖b n z‖) M)) ∂μ
        ≤ ∫⁻ z, ENNReal.ofReal ((2 * C / M) * ‖b n z‖ ^ 2) ∂μ := lintegral_mono_ae hpt
      _ = ENNReal.ofReal (2 * C / M) * ∫⁻ z, ENNReal.ofReal (‖b n z‖ ^ 2) ∂μ := by
            rw [← lintegral_const_mul'' (ENNReal.ofReal (2 * C / M)) hconst_meas]
            apply lintegral_congr
            intro z
            rw [ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal (2 * C / M) * ENNReal.ofReal (B ^ 2) := by
            gcongr
            exact hB n
      _ = ENNReal.ofReal (2 * C / M * B ^ 2) := by
            rw [← ENNReal.ofReal_mul (by positivity)]
      _ = ENNReal.ofReal (K / M) := by
            rw [hKdef]; congr 1; ring
      _ ≤ ε / 2 := hMbound
  have hAev : ∀ᶠ n in atTop, (∫⁻ z,
      ENNReal.ofReal (C * ‖ν n z‖ * min (‖b n z‖) M) ∂μ) ≤ ε / 2 :=
    (ENNReal.tendsto_nhds_zero.mp hA) (ε / 2) (ENNReal.half_pos hε0)
  filter_upwards [hAev] with n hn
  have hsplit : ∫⁻ z, ENNReal.ofReal (C * ‖ν n z‖ * ‖b n z‖) ∂μ
      = (∫⁻ z, ENNReal.ofReal (C * ‖ν n z‖ * min (‖b n z‖) M) ∂μ)
        + ∫⁻ z, ENNReal.ofReal (C * ‖ν n z‖ * (‖b n z‖ - min (‖b n z‖) M)) ∂μ := by
    rw [← lintegral_add_left' (hGmeas n)]
    apply lintegral_congr
    intro z
    exact ofReal_mul_min_decomp hC hMpos.le (norm_nonneg _) (norm_nonneg _)
  rw [hsplit]
  calc (∫⁻ z, ENNReal.ofReal (C * ‖ν n z‖ * min (‖b n z‖) M) ∂μ)
        + ∫⁻ z, ENNReal.ofReal (C * ‖ν n z‖ * (‖b n z‖ - min (‖b n z‖) M)) ∂μ
      ≤ ε / 2 + ε / 2 := add_le_add hn (hHbound n)
    _ = ε := ENNReal.add_halves ε

end Work.MRMT.Found
