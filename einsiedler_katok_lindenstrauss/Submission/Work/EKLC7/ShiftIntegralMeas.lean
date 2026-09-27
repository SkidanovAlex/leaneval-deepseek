import Mathlib

namespace Work.EKLC7

open MeasureTheory

theorem ShiftIntegralMeas (h : CompactlySupportedContinuousMap ℝ ℝ) (Cp : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsFiniteMeasureOnCompacts Cp] :
    Measurable (fun z : ℝ × ℝ => ∫ q, (h : ℝ → ℝ) (z.1 * z.2 + q) ∂Cp) ∧
    (∀ M : ℝ, ∃ C : ℝ, ∀ z : ℝ × ℝ, |z.1| ≤ M → |z.2| ≤ M →
      |∫ q, (h : ℝ → ℝ) (z.1 * z.2 + q) ∂Cp| ≤ C) := by
  constructor
  · -- Measurability: the integrand is jointly continuous, hence measurable; the parametric
    -- Bochner integral of a strongly measurable curried function is strongly measurable.
    have hcont : Continuous (fun p : (ℝ × ℝ) × ℝ => (h : ℝ → ℝ) (p.1.1 * p.1.2 + p.2)) := by
      apply Continuous.comp
      · exact map_continuous h
      · fun_prop
    exact hcont.stronglyMeasurable.integral_prod_right.measurable
  · intro M
    -- A radius outside which `h` vanishes.
    obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ x : ℝ, R < |x| → (h : ℝ → ℝ) x = 0 := by
      obtain ⟨r, hr⟩ := h.hasCompactSupport.isCompact.isBounded.subset_closedBall (0 : ℝ)
      refine ⟨r, fun x hx => image_eq_zero_of_notMem_tsupport fun hmem => ?_⟩
      have hxr : |x| ≤ r := by
        have := Metric.mem_closedBall.mp (hr hmem)
        simpa [dist_zero_right, Real.norm_eq_abs] using this
      linarith
    -- A uniform bound for `h`.
    obtain ⟨Mf, hMf⟩ : ∃ Mf : ℝ, ∀ x : ℝ, |(h : ℝ → ℝ) x| ≤ Mf := by
      obtain ⟨r, hr⟩ :=
        (h.hasCompactSupport.isCompact_range (map_continuous h)).isBounded.subset_closedBall (0 : ℝ)
      refine ⟨r, fun x => ?_⟩
      have := Metric.mem_closedBall.mp (hr (Set.mem_range_self x))
      simpa [Real.dist_eq] using this
    by_cases hM : M < 0
    · -- Vacuous case: no `z` with `|z.1| ≤ M`.
      refine ⟨0, fun z h1 h2 => ?_⟩
      exfalso
      linarith [abs_nonneg z.1]
    · have hM : 0 ≤ M := not_lt.mp hM
      refine ⟨Mf * Cp.real (Set.Icc (-(R + M * M)) (R + M * M)), fun z h1 h2 => ?_⟩
      set B : ℝ := M * M with hBdef
      set S : Set ℝ := Set.Icc (-(R + B)) (R + B) with hSdef
      have hSmeas : MeasurableSet S := by rw [hSdef]; exact measurableSet_Icc
      have hSfin : Cp S < ⊤ := by rw [hSdef]; exact isCompact_Icc.measure_lt_top
      have hSne : Cp S ≠ ⊤ := ne_of_lt hSfin
      have hw : |z.1 * z.2| ≤ B := by
        rw [abs_mul, hBdef]
        exact mul_le_mul h1 h2 (abs_nonneg z.2) hM
      -- Pointwise domination of the integrand by an integrable function.
      have hpt : ∀ q : ℝ, |(h : ℝ → ℝ) (z.1 * z.2 + q)| ≤ S.indicator (fun _ => Mf) q := by
        intro q
        by_cases hq : q ∈ S
        · rw [Set.indicator_of_mem hq]; exact hMf _
        · rw [Set.indicator_of_notMem hq]
          have hq' : R + B < |q| := by
            have hq'' : q < -(R + B) ∨ R + B < q := by
              rw [hSdef] at hq
              simpa only [Set.mem_Icc, not_and_or, not_le] using hq
            rcases hq'' with h | h
            · have : R + B < -q := by linarith
              linarith [neg_le_abs q]
            · linarith [le_abs_self q]
          have hlowaux : |q| - |z.1 * z.2| ≤ |z.1 * z.2 + q| := by
            have := abs_sub_abs_le_abs_sub q (-(z.1 * z.2))
            simpa only [abs_neg, sub_neg_eq_add, add_comm] using this
          have hlow : R < |z.1 * z.2 + q| := by linarith
          simp [hR _ hlow]
      have step1 : |∫ q, (h : ℝ → ℝ) (z.1 * z.2 + q) ∂Cp|
          ≤ ∫ q, |(h : ℝ → ℝ) (z.1 * z.2 + q)| ∂Cp := by
        simpa only [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (fun q : ℝ => (h : ℝ → ℝ) (z.1 * z.2 + q)) (μ := Cp)
      calc |∫ q, (h : ℝ → ℝ) (z.1 * z.2 + q) ∂Cp|
          ≤ ∫ q, |(h : ℝ → ℝ) (z.1 * z.2 + q)| ∂Cp := step1
        _ ≤ ∫ q, S.indicator (fun _ => Mf) q ∂Cp := by
              apply integral_mono_of_nonneg
              · exact Filter.Eventually.of_forall fun q => abs_nonneg _
              · exact (integrableOn_const (C := Mf) (μ := Cp) (s := S) hSne).integrable_indicator
                  hSmeas
              · exact Filter.Eventually.of_forall hpt
        _ = Mf * Cp.real S := by
              rw [integral_indicator_const Mf hSmeas, smul_eq_mul, mul_comm]

end Work.EKLC7
