import Mathlib.MeasureTheory.Integral.Prod
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR.Rb5Lin

open MeasureTheory

/-- Pointwise identification of the inner integrand on the left-hand side of
`triangular_swap` with the indicator of the triangular region `|p.1| < p.2`. -/
private lemma indicator_Ioi_abs_eq (F : ℝ → ℝ → ℝ) (s : ℝ) :
    (Set.Ioi |s|).indicator (fun r => F s r)
      = fun r => ({p : ℝ × ℝ | |p.1| < p.2}.indicator (fun p => F p.1 p.2)) (s, r) := by
  funext r
  by_cases h : |s| < r
  · simp [Set.indicator_of_mem, h]
  · simp [Set.indicator_of_notMem, h]

/-- Pointwise identification of the inner integrand on the right-hand side of
`triangular_swap` with the indicator of the triangular region `|p.1| < p.2`.
Note that `Set.Ioo (-r) r = {s | |s| < r}` holds for every real `r`. -/
private lemma indicator_Ioo_abs_eq (F : ℝ → ℝ → ℝ) (r : ℝ) :
    (Set.Ioo (-r) r).indicator (fun s => F s r)
      = fun s => ({p : ℝ × ℝ | |p.1| < p.2}.indicator (fun p => F p.1 p.2)) (s, r) := by
  funext s
  have hmem : s ∈ Set.Ioo (-r) r ↔ |s| < r := by simp [abs_lt]
  by_cases h : s ∈ Set.Ioo (-r) r
  · have h2 : |s| < r := hmem.mp h
    simp [Set.indicator_of_mem, h, h2]
  · have h2 : ¬ (|s| < r) := fun hc => h (hmem.mpr hc)
    simp [Set.indicator_of_notMem, h, h2]

theorem triangular_swap {F : ℝ → ℝ → ℝ}
    (hF : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2)
      {p : ℝ × ℝ | |p.1| < p.2} MeasureTheory.volume) :
    (∫ s : ℝ, ∫ r in Set.Ioi |s|, F s r)
      = ∫ r in Set.Ioi (0 : ℝ), ∫ s in Set.Ioo (-r) r, F s r := by
  have hSmeas : MeasurableSet ({p : ℝ × ℝ | |p.1| < p.2}) :=
    (isOpen_lt (continuous_abs.comp continuous_fst) continuous_snd).measurableSet
  let G : ℝ × ℝ → ℝ :=
    fun p => ({p : ℝ × ℝ | |p.1| < p.2}.indicator (fun p : ℝ × ℝ => F p.1 p.2)) p
  have hGint : Integrable G (volume : Measure (ℝ × ℝ)) :=
    (integrable_indicator_iff hSmeas).2 hF
  have hprod : (∫ p : ℝ × ℝ, G p) = ∫ s : ℝ, ∫ r : ℝ, G (s, r) := integral_prod _ hGint
  have hprod' : (∫ p : ℝ × ℝ, G p) = ∫ r : ℝ, ∫ s : ℝ, G (s, r) :=
    integral_prod_symm _ hGint
  have hL : (∫ s : ℝ, ∫ r in Set.Ioi |s|, F s r) = ∫ p : ℝ × ℝ, G p := by
    rw [hprod]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    dsimp only
    rw [← integral_indicator measurableSet_Ioi]
    rw [indicator_Ioi_abs_eq F s]
  have hR : (∫ r in Set.Ioi (0 : ℝ), ∫ s in Set.Ioo (-r) r, F s r)
      = ∫ p : ℝ × ℝ, G p := by
    rw [hprod']
    rw [← integral_indicator measurableSet_Ioi]
    refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
    dsimp only
    by_cases hr : 0 < r
    · rw [Set.indicator_of_mem (show r ∈ Set.Ioi (0 : ℝ) from hr)]
      rw [← integral_indicator measurableSet_Ioo]
      rw [indicator_Ioo_abs_eq F r]
    · rw [Set.indicator_of_notMem (show r ∉ Set.Ioi (0 : ℝ) from hr)]
      have hzero : (fun s => G (s, r)) = fun _ => (0 : ℝ) := by
        funext s
        have hs : ¬ (|s| < r) := by
          intro hc
          have h1 : (0 : ℝ) ≤ |s| := abs_nonneg s
          linarith
        simp [G, Set.indicator_of_notMem, hs]
      rw [hzero]
      simp
  rw [hL, hR]

end Work.BoseFixR.Rb5Lin
