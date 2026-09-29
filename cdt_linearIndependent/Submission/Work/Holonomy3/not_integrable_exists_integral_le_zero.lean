import Mathlib

namespace Work.Holonomy3

open MeasureTheory

/-- If `u n ↓ f` pointwise, each `u n` is integrable and bounded above by `C`, and `f` is not
integrable, then some `u n` has non-positive integral.

Indeed, since `f ≤ C` the positive part of `f` has finite integral, so the non-integrability of `f`
forces `∫⁻ f⁻ = ∞`. Monotone convergence gives `∫⁻ (u n)⁻ → ∞`, and since
`∫⁻ (u n)⁺ ≤ C < ∞` the sequence of (real) integrals `∫ u n` is eventually negative. -/
theorem not_integrable_exists_integral_le_zero {X : Type*} [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    [MeasureTheory.IsProbabilityMeasure μ] {f : X → ℝ} {C : ℝ} (hC : 0 ≤ C)
    {u : ℕ → X → ℝ} (hu : ∀ n, MeasureTheory.Integrable (u n) μ)
    (huC : ∀ n x, u n x ≤ C)
    (huf : ∀ n x, f x ≤ u n x)
    (hmono : ∀ x, Antitone (fun n => u n x))
    (htend : ∀ x, Filter.Tendsto (fun n => u n x) Filter.atTop (nhds (f x)))
    (hni : ¬ MeasureTheory.Integrable f μ) :
    ∃ n, ∫ x, u n x ∂μ ≤ 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  -- `f` is a pointwise limit of integrable (hence ae-strongly-measurable) functions.
  have hf_sm : AEStronglyMeasurable f μ :=
    aestronglyMeasurable_of_tendsto_ae Filter.atTop
      (fun n => (hu n).aestronglyMeasurable) (Filter.Eventually.of_forall htend)
  have hf_ae : AEMeasurable f μ :=
    aemeasurable_of_tendsto_metrizable_ae' (fun n => (hu n).aemeasurable)
      (Filter.Eventually.of_forall htend)
  have hf_notfin : ¬ MeasureTheory.HasFiniteIntegral f μ := fun hfin => hni ⟨hf_sm, hfin⟩
  have hnorm_top : ∫⁻ x, ‖f x‖ₑ ∂μ = ⊤ := by
    rw [MeasureTheory.hasFiniteIntegral_def] at hf_notfin
    exact top_le_iff.mp (not_lt.mp hf_notfin)
  -- The negative part of `f` has infinite lintegral: `f` is bounded above by `C`.
  have hB_top : ∫⁻ x, ENNReal.ofReal (-(f x)) ∂μ = ⊤ := by
    have hkey : ∀ a : ℝ, ENNReal.ofReal ‖a‖ = ENNReal.ofReal a + ENNReal.ofReal (-a) := by
      intro a
      rw [Real.norm_eq_abs]
      rcases lt_or_ge 0 a with ha | ha
      · rw [abs_of_pos ha, ENNReal.ofReal_eq_zero.mpr (by linarith : -a ≤ 0)]
        simp
      · rw [abs_of_nonpos ha, ENNReal.ofReal_eq_zero.mpr (by linarith : a ≤ 0)]
        simp
    have hsplit : ∫⁻ x, ENNReal.ofReal ‖f x‖ ∂μ
        = ∫⁻ x, (ENNReal.ofReal (f x) + ENNReal.ofReal (-(f x))) ∂μ :=
      MeasureTheory.lintegral_congr (fun x => hkey (f x))
    have hadd : ∫⁻ x, (ENNReal.ofReal (f x) + ENNReal.ofReal (-(f x))) ∂μ
        = ∫⁻ x, ENNReal.ofReal (f x) ∂μ + ∫⁻ x, ENNReal.ofReal (-(f x)) ∂μ :=
      MeasureTheory.lintegral_add_left'
        (Measurable.comp_aemeasurable ENNReal.measurable_ofReal hf_ae) _
    have hnorm_ofReal : ∫⁻ x, ENNReal.ofReal ‖f x‖ ∂μ = ⊤ := by
      have hcongr : ∫⁻ x, ENNReal.ofReal ‖f x‖ ∂μ = ∫⁻ x, ‖f x‖ₑ ∂μ :=
        MeasureTheory.lintegral_congr (fun x => ofReal_norm (f x))
      rw [hcongr]; exact hnorm_top
    have hsum : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) + (∫⁻ x, ENNReal.ofReal (-(f x)) ∂μ) = ⊤ := by
      rw [← hadd, ← hsplit]; exact hnorm_ofReal
    have hAfin : ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≠ ⊤ := by
      have hAle : ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤ ENNReal.ofReal C := by
        calc ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤ ∫⁻ x, ENNReal.ofReal C ∂μ :=
              MeasureTheory.lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (le_trans (huf 0 x) (huC 0 x)))
          _ = ENNReal.ofReal C := by simp [MeasureTheory.lintegral_const]
      exact (lt_of_le_of_lt hAle ENNReal.ofReal_lt_top).ne
    rcases ENNReal.add_eq_top.mp hsum with h | h
    · exact absurd h hAfin
    · exact h
  -- Monotone convergence of the negative parts of `u n`.
  have hg_meas : ∀ n, AEMeasurable (fun x => ENNReal.ofReal (-(u n x))) μ := by
    intro n
    apply Measurable.comp_aemeasurable ENNReal.measurable_ofReal
    exact Measurable.comp_aemeasurable measurable_neg (hu n).aemeasurable
  have hmono' : ∀ᵐ x ∂μ, Monotone (fun n => ENNReal.ofReal (-(u n x))) :=
    Filter.Eventually.of_forall (fun x a b hab => ENNReal.ofReal_le_ofReal (neg_le_neg (hmono x hab)))
  have htend' : ∀ᵐ x ∂μ,
      Filter.Tendsto (fun n => ENNReal.ofReal (-(u n x))) Filter.atTop (nhds (ENNReal.ofReal (-(f x)))) :=
    Filter.Eventually.of_forall (fun x =>
      (ENNReal.continuous_ofReal.tendsto _).comp (htend x).neg)
  have hlim : Filter.Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (-(u n x)) ∂μ) Filter.atTop
      (nhds (∫⁻ x, ENNReal.ofReal (-(f x)) ∂μ)) :=
    MeasureTheory.lintegral_tendsto_of_tendsto_of_monotone hg_meas hmono' htend'
  rw [hB_top] at hlim
  have hgt : ∀ᶠ n in Filter.atTop, ENNReal.ofReal C < ∫⁻ x, ENNReal.ofReal (-(u n x)) ∂μ :=
    hlim.eventually (isOpen_Ioi.mem_nhds ENNReal.ofReal_lt_top)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hgt
  have hBNgt : ENNReal.ofReal C < ∫⁻ x, ENNReal.ofReal (-(u N x)) ∂μ := hN N le_rfl
  -- The negative part of `u N` has finite lintegral, since `u N` is integrable.
  have hBNfin : ∫⁻ x, ENNReal.ofReal (-(u N x)) ∂μ ≠ ⊤ := by
    have hle : ∫⁻ x, ENNReal.ofReal (-(u N x)) ∂μ ≤ ∫⁻ x, ‖u N x‖ₑ ∂μ :=
      MeasureTheory.lintegral_mono (fun x => by
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (by simpa [Real.norm_eq_abs] using neg_le_abs (u N x)))
    exact (lt_of_le_of_lt hle (hu N).hasFiniteIntegral).ne
  -- Conclude `∫ u N < 0`, contradicting the assumption.
  have hC_lt : C < (∫⁻ x, ENNReal.ofReal (-(u N x)) ∂μ).toReal := by
    have h := (ENNReal.toReal_lt_toReal ENNReal.ofReal_lt_top.ne hBNfin).mpr hBNgt
    simpa [ENNReal.toReal_ofReal hC] using h
  have hANle : (∫⁻ x, ENNReal.ofReal (u N x) ∂μ).toReal ≤ C := by
    have hAle : ∫⁻ x, ENNReal.ofReal (u N x) ∂μ ≤ ENNReal.ofReal C := by
      calc ∫⁻ x, ENNReal.ofReal (u N x) ∂μ ≤ ∫⁻ x, ENNReal.ofReal C ∂μ :=
            MeasureTheory.lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (huC N x))
        _ = ENNReal.ofReal C := by simp [MeasureTheory.lintegral_const]
    have h := ENNReal.toReal_mono ENNReal.ofReal_lt_top.ne hAle
    simpa [ENNReal.toReal_ofReal hC] using h
  have hint := MeasureTheory.integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hu N)
  have hneg : ∫ x, u N x ∂μ < 0 := by rw [hint]; linarith
  linarith [hcon N, hneg]

end Work.Holonomy3
