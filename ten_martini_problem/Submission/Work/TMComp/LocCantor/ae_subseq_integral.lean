import Mathlib

open MeasureTheory Filter Set

namespace Work.TMComp.LocCantor

/-- Helper: the Markov / Chebyshev bound for the restricted Lebesgue measure on `(0,1]`.

For an integrable function `f` that is nonnegative a.e. w.r.t. the restricted measure, the
measure of `{x | ε ≤ |f x|}` is bounded by `∫ f / ε` (as an `ℝ≥0∞`-valued quantity).  This is
the only place where the a.e. nonnegativity hypothesis is used. -/
private lemma meas_abs_ge_le_ofReal_div (F : ℕ → ℝ → ℝ) (j : ℕ) {ε : ℝ} (hε : 0 < ε)
    (hFj : 0 ≤ᵐ[((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1))] F j)
    (hintj : IntegrableOn (F j) (Set.Ioc (0 : ℝ) 1)) :
    ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)) {x | ε ≤ |F j x|}
      ≤ ENNReal.ofReal ((∫ x, F j x ∂((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1))) / ε) := by
  have hmeas : AEMeasurable (fun x => ENNReal.ofReal |F j x|)
      ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)) :=
    (hintj.aestronglyMeasurable.aemeasurable.abs).ennreal_ofReal
  have key := meas_ge_le_lintegral_div hmeas
    (ENNReal.ofReal_ne_zero_iff.mpr hε) ENNReal.ofReal_ne_top
  have hset : {x | ε ≤ |F j x|} = {x | ENNReal.ofReal ε ≤ ENNReal.ofReal |F j x|} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    rw [ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)]
  have hlint : ∫⁻ x, ENNReal.ofReal |F j x| ∂((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1))
      = ENNReal.ofReal (∫ x, F j x ∂((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1))) := by
    have h1 : ∫⁻ x, ENNReal.ofReal |F j x| ∂((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1))
        = ∫⁻ x, ENNReal.ofReal (F j x) ∂((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)) := by
      apply lintegral_congr_ae
      filter_upwards [hFj] with x hx
      rw [abs_of_nonneg hx]
    rw [h1]
    exact (ofReal_integral_eq_lintegral_ofReal hintj hFj).symm
  calc ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)) {x | ε ≤ |F j x|}
      = ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)) {x | ENNReal.ofReal ε ≤ ENNReal.ofReal |F j x|} := by rw [hset]
    _ ≤ (∫⁻ x, ENNReal.ofReal |F j x| ∂((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1))) / ENNReal.ofReal ε := key
    _ = ENNReal.ofReal ((∫ x, F j x ∂((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1))) / ε) := by
          rw [hlint, ENNReal.ofReal_div_of_pos hε]

theorem ae_subseq_integral {F : ℕ → ℝ → ℝ} (hF : ∀ j : ℕ, 0 ≤ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)] F j) (hint : ∀ j : ℕ, MeasureTheory.IntegrableOn (F j) (Set.Ioc (0 : ℝ) 1)) (h : Filter.Tendsto (fun j : ℕ => ∫ y in (0 : ℝ)..1, F j y) Filter.atTop (nhds 0)) : ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ y ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)), Filter.Tendsto (fun j : ℕ => F (φ j) y) Filter.atTop (nhds 0) := by
  -- Rewrite the hypothesis as convergence of the integrals w.r.t. the restricted measure.
  have hμ : Tendsto (fun j => ∫ x, F j x ∂((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)))
      atTop (nhds 0) := by
    have heq : ∀ j, (∫ y in (0 : ℝ)..1, F j y)
        = ∫ x, F j x ∂((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)) := fun j => by
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    simpa only [heq] using h
  -- Convergence in measure to zero, via Markov's inequality.
  have hTIM : TendstoInMeasure ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)) F atTop
      (0 : ℝ → ℝ) := by
    rw [tendstoInMeasure_iff_dist]
    intro ε hε
    have hbound : ∀ j, ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1))
        {x | ε ≤ dist (F j x) 0}
        ≤ ENNReal.ofReal
            ((∫ x, F j x ∂((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1))) / ε) := by
      intro j
      have hset2 : {x | ε ≤ dist (F j x) 0} = {x | ε ≤ |F j x|} := by
        ext x; simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero]
      rw [hset2]
      exact meas_abs_ge_le_ofReal_div F j hε (hF j) (hint j)
    have hb : Tendsto (fun j => ENNReal.ofReal
        ((∫ x, F j x ∂((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1))) / ε))
        atTop (nhds 0) := by
      have hr : Tendsto (fun j =>
          (∫ x, F j x ∂((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1))) / ε)
          atTop (nhds 0) := by
        simpa using hμ.div_const ε
      have hc := (ENNReal.continuous_ofReal.tendsto 0).comp hr
      simpa only [Function.comp_def, ENNReal.ofReal_zero] using hc
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
      (fun j => zero_le) hbound
  -- Extract an almost-everywhere convergent subsequence.
  obtain ⟨φ, hφ, hconv⟩ := hTIM.exists_seq_tendsto_ae
  exact ⟨φ, hφ, by simpa using hconv⟩

end Work.TMComp.LocCantor
