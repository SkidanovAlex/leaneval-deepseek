import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace Commons.MeasureTheory.IntervalIntegral

theorem integral_indicator_Ici (C h : ℝ) {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b, (if h ≤ t then C else 0)) = C * max (b - max a h) 0 := by
  rw [intervalIntegral.integral_of_le hab]
  rw [MeasureTheory.setIntegral_congr_set
    (MeasureTheory.Ioc_ae_eq_Icc (μ := MeasureTheory.volume) (a := a) (b := b))]
  have h1 : (fun t : ℝ => (if h ≤ t then C else 0)) = (Set.Ici h).indicator (fun _ => C) := by
    funext t
    by_cases hh : h ≤ t
    · rw [if_pos hh, Set.indicator_of_mem (Set.mem_Ici.mpr hh)]
    · rw [if_neg hh, Set.indicator_of_notMem (by simpa [Set.mem_Ici] using hh)]
  rw [h1]
  rw [MeasureTheory.setIntegral_indicator measurableSet_Ici]
  have hset : Set.Icc a b ∩ Set.Ici h = Set.Icc (max a h) b := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ici]
    constructor
    · rintro ⟨⟨hat, htb⟩, hht⟩; exact ⟨max_le hat hht, htb⟩
    · rintro ⟨hmt, htb⟩
      exact ⟨⟨le_trans (le_max_left _ _) hmt, htb⟩, le_trans (le_max_right _ _) hmt⟩
  rw [hset, MeasureTheory.setIntegral_const, Real.volume_real_Icc, smul_eq_mul, mul_comm]

end Commons.MeasureTheory.IntervalIntegral