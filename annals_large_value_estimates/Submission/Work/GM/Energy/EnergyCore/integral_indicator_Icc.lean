import Mathlib

open MeasureTheory

set_option linter.unusedVariables false

namespace Work.GM.Energy.EnergyCore

theorem integral_indicator_Icc {h : ℝ → ℝ} {a b c d : ℝ} (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b)
    (hh : ContinuousOn h (Set.Icc a b)) :
    ∫ x in a..b, (if c ≤ x ∧ x ≤ d then h x else 0) = ∫ x in c..d, h x := by
  have hab : a ≤ b := hac.trans (hcd.trans hdb)
  -- The integrand is the indicator of `[c,d]` applied to `h`.
  have hIcc : (fun x => (if c ≤ x ∧ x ≤ d then h x else 0))
      = Set.indicator (Set.Icc c d) h := by
    funext x
    rw [Set.indicator_apply]
    by_cases hx : c ≤ x ∧ x ≤ d
    · rw [if_pos hx, if_pos (by simpa [Set.mem_Icc] using hx)]
    · rw [if_neg hx, if_neg (by simpa [Set.mem_Icc] using hx)]
  rw [hIcc]
  -- Replacing the indicator of `[c,d]` by the indicator of `(c,d]` changes the function
  -- at most at the single point `c`.
  have step1 : ∫ x in a..b, Set.indicator (Set.Icc c d) h x
      = ∫ x in a..b, Set.indicator (Set.Ioc c d) h x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [MeasureTheory.Measure.ae_ne (volume : Measure ℝ) c] with x hx _
    by_cases hmem : x ∈ Set.Icc c d
    · have hmem' : x ∈ Set.Ioc c d := ⟨lt_of_le_of_ne hmem.1 (Ne.symm hx), hmem.2⟩
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem']
    · have hmem' : x ∉ Set.Ioc c d := fun hh => hmem ⟨le_of_lt hh.1, hh.2⟩
      rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem']
  rw [step1]
  -- Turn the interval integral into a set integral over `(a,b]`, absorb the indicator.
  rw [intervalIntegral.integral_of_le hab]
  rw [MeasureTheory.setIntegral_indicator measurableSet_Ioc]
  have hset : Set.Ioc a b ∩ Set.Ioc c d = Set.Ioc c d := by
    ext x; constructor
    · exact fun hx => hx.2
    · exact fun hx => ⟨⟨lt_of_le_of_lt hac hx.1, le_trans hx.2 hdb⟩, hx⟩
  rw [hset]
  rw [← intervalIntegral.integral_of_le hcd]

end Work.GM.Energy.EnergyCore
