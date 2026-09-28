import Mathlib

namespace Work.HP.BallConeK

open MeasureTheory intervalIntegral

/-- For `c ∈ [Y,T]`, the interval integral of `g` against the indicator of `{t | c ≤ t}`
over `[Y,T]` equals the interval integral of `g` over `[c,T]`. -/
private lemma perA_integral {c Y T : ℝ} (g : ℝ → ℝ) (hYT : Y ≤ T) (hYc : Y ≤ c)
    (hcT : c ≤ T) (hg : ContinuousOn g (Set.Icc Y T)) :
    ∫ t in Y..T, g t * (if c ≤ t then (1 : ℝ) else 0) = ∫ t in c..T, g t := by
  have huic : Set.uIcc Y T = Set.Icc Y T := Set.uIcc_of_le hYT
  have huic2 : Set.uIcc c T = Set.Icc c T := Set.uIcc_of_le hcT
  have hcontCT : ContinuousOn g (Set.Icc c T) := hg.mono (Set.Icc_subset_Icc hYc le_rfl)
  have hInt : Integrable ((Set.Icc c T).indicator g) volume :=
    (hcontCT.integrableOn_compact isCompact_Icc).integrable_indicator measurableSet_Icc
  have hstep1 : ∫ t in Y..T, g t * (if c ≤ t then (1 : ℝ) else 0)
      = ∫ t in Y..T, (Set.Icc c T).indicator g t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [huic] at ht
    rw [Set.indicator_apply]
    by_cases hct : c ≤ t
    · have hmem : t ∈ Set.Icc c T := ⟨hct, ht.2⟩
      simp [hct, hmem]
    · have hmem : t ∉ Set.Icc c T := fun h => hct h.1
      simp [hct, hmem]
  have hzero : ∫ t in Y..c, (Set.Icc c T).indicator g t = 0 := by
    apply intervalIntegral.integral_zero_ae
    have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ c := by
      rw [MeasureTheory.ae_iff]
      have : {x : ℝ | ¬ x ≠ c} = {c} := by ext x; simp
      rw [this]
      exact MeasureTheory.measure_singleton c
    filter_upwards [hne] with x hxne hx
    rw [Set.indicator_apply]
    have hxle : x ≤ c := by
      have := hx; rw [Set.uIoc_of_le hYc] at this; exact this.2
    have hxnot : x ∉ Set.Icc c T := fun h => hxne (le_antisymm hxle h.1)
    simp [hxnot]
  have hcT' : ∫ t in c..T, (Set.Icc c T).indicator g t = ∫ t in c..T, g t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [huic2] at ht
    exact Set.indicator_of_mem ht g
  have hadj := intervalIntegral.integral_add_adjacent_intervals
      (hInt.intervalIntegrable (μ := volume) (a := Y) (b := c))
      (hInt.intervalIntegrable (μ := volume) (a := c) (b := T))
  rw [hstep1]
  rw [← hadj, hzero, hcT', zero_add]

/-- The function `g * 1_{[c,∞)}` is interval integrable on `[Y,T]` when `c ∈ [Y,T]` and
`g` is continuous there. -/
private lemma perA_integrable {c Y T : ℝ} (g : ℝ → ℝ) (hYT : Y ≤ T) (hYc : Y ≤ c)
    (_hcT : c ≤ T) (hg : ContinuousOn g (Set.Icc Y T)) :
    IntervalIntegrable (fun t => g t * (if c ≤ t then (1 : ℝ) else 0)) volume Y T := by
  have hcontCT : ContinuousOn g (Set.Icc c T) := hg.mono (Set.Icc_subset_Icc hYc le_rfl)
  have hInt : Integrable ((Set.Icc c T).indicator g) volume :=
    (hcontCT.integrableOn_compact isCompact_Icc).integrable_indicator measurableSet_Icc
  refine IntervalIntegrable.congr ?_ (hInt.intervalIntegrable (μ := volume) (a := Y) (b := T))
  intro t ht
  rw [Set.uIoc_of_le hYT] at ht
  rw [Set.indicator_apply]
  by_cases hct : c ≤ t
  · have hmem : t ∈ Set.Icc c T := ⟨hct, ht.2⟩
    simp [hct, hmem]
  · have hmem : t ∉ Set.Icc c T := fun h => hct h.1
    simp [hct, hmem]

theorem layerCake {α : Type*} (F : Finset α) (rr : α → ℝ) (Y T : ℝ) (g : ℝ → ℝ)
    (hYT : Y ≤ T) (hY : ∀ a ∈ F, Y ≤ rr a) (hT : ∀ a ∈ F, rr a ≤ T)
    (hg : ContinuousOn g (Set.Icc Y T)) :
    ∑ a ∈ F, ∫ t in (rr a)..T, g t
      = ∫ t in Y..T, g t * ((F.filter (fun a => rr a ≤ t)).card : ℝ) := by
  have key : ∀ a ∈ F, ∫ t in Y..T, g t * (if rr a ≤ t then (1 : ℝ) else 0)
      = ∫ t in (rr a)..T, g t :=
    fun a ha => perA_integral g hYT (hY a ha) (hT a ha) hg
  have hint : ∀ a ∈ F,
      IntervalIntegrable (fun t => g t * (if rr a ≤ t then (1 : ℝ) else 0)) volume Y T :=
    fun a ha => perA_integrable g hYT (hY a ha) (hT a ha) hg
  have hR : ∫ t in Y..T, g t * ((F.filter (fun a => rr a ≤ t)).card : ℝ)
      = ∑ a ∈ F, ∫ t in Y..T, g t * (if rr a ≤ t then (1 : ℝ) else 0) := by
    calc ∫ t in Y..T, g t * ((F.filter (fun a => rr a ≤ t)).card : ℝ)
        = ∫ t in Y..T, g t * (∑ a ∈ F, (if rr a ≤ t then (1 : ℝ) else 0)) := by
            apply intervalIntegral.integral_congr
            intro t _
            show g t * ((F.filter (fun a => rr a ≤ t)).card : ℝ)
                = g t * (∑ a ∈ F, (if rr a ≤ t then (1 : ℝ) else 0))
            rw [Finset.natCast_card_filter]
        _ = ∫ t in Y..T, ∑ a ∈ F, g t * (if rr a ≤ t then (1 : ℝ) else 0) := by
            apply intervalIntegral.integral_congr
            intro t _
            show g t * (∑ a ∈ F, (if rr a ≤ t then (1 : ℝ) else 0))
                = ∑ a ∈ F, g t * (if rr a ≤ t then (1 : ℝ) else 0)
            rw [Finset.mul_sum]
        _ = ∑ a ∈ F, ∫ t in Y..T, g t * (if rr a ≤ t then (1 : ℝ) else 0) :=
            intervalIntegral.integral_finsetSum hint
  rw [hR]
  exact (Finset.sum_congr rfl key).symm

end Work.HP.BallConeK
