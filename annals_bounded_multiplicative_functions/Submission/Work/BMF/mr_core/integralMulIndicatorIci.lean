import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_core

theorem integralMulIndicatorIci (f : ℝ → ℂ) (a c b : ℝ) (hac : a ≤ c) (hcb : c ≤ b) :
    (∫ t in a..b, f t * (if c ≤ t then (1 : ℂ) else 0)) = ∫ t in c..b, f t := by
  -- Rewrite the integrand pointwise as the indicator of `Set.Ici c` applied to `f`.
  have hfun : ∀ t, f t * (if c ≤ t then (1 : ℂ) else 0) = Set.indicator (Set.Ici c) f t := by
    intro t
    by_cases h : c ≤ t <;> simp [Set.mem_Ici, h]
  rw [intervalIntegral.integral_congr (fun t _ => hfun t)]
  -- `Set.indicator (Set.Ici c) f` and `Set.indicator (Set.Ioi c) f` agree off `{c}`.
  have hind : ∀ x, x ≠ c → Set.indicator (Set.Ici c) f x = Set.indicator (Set.Ioi c) f x := by
    intro x hx
    rcases lt_or_ge x c with h | h
    · rw [Set.indicator_of_notMem (by simp [Set.mem_Ici, not_le.mpr h]),
          Set.indicator_of_notMem (by simp [Set.mem_Ioi, not_lt.mpr (le_of_lt h)])]
    · rw [Set.indicator_of_mem (by simp [Set.mem_Ici, h]),
          Set.indicator_of_mem (by simp [Set.mem_Ioi, lt_of_le_of_ne h (Ne.symm hx)])]
  have hae : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), x ∈ Set.uIoc a b →
      Set.indicator (Set.Ici c) f x = Set.indicator (Set.Ioi c) f x := by
    rw [MeasureTheory.ae_iff]
    apply MeasureTheory.measure_mono_null (t := {c}) _ Real.volume_singleton
    intro x hx
    simp only [Set.mem_singleton_iff] at hx ⊢
    by_contra hne
    exact hx (fun _ => hind x hne)
  rw [intervalIntegral.integral_congr_ae hae]
  -- `Set.Ioi c ∩ Set.Ioc a b = Set.Ioc c b`, so the interval integral collapses to `c..b`.
  have hset : Set.Ioi c ∩ Set.Ioc a b = Set.Ioc c b := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ioc]
    constructor
    · rintro ⟨hcx, _, hxb⟩; exact ⟨hcx, hxb⟩
    · rintro ⟨hcx, hxb⟩; exact ⟨hcx, lt_of_le_of_lt hac hcx, hxb⟩
  rw [intervalIntegral.integral_of_le (hac.trans hcb), intervalIntegral.integral_of_le hcb]
  rw [MeasureTheory.integral_indicator measurableSet_Ioi,
      MeasureTheory.Measure.restrict_restrict measurableSet_Ioi, hset]

end Work.BMF.mr_core
