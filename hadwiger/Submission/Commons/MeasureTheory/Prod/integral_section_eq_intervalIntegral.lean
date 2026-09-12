import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory

namespace Commons.MeasureTheory.Prod

theorem integral_section_eq_intervalIntegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureTheory.MeasureSpace E] {A : Set (ℝ × E)} {a b : ℝ} (hab : a ≤ b)
    (hA : A ⊆ Set.Icc a b ×ˢ Set.univ) :
    ∫ s, (MeasureTheory.volume (Prod.mk s ⁻¹' A)).toReal
      = ∫ s in a..b, (MeasureTheory.volume (Prod.mk s ⁻¹' A)).toReal := by
  set f : ℝ → ℝ := fun s => (MeasureTheory.volume (Prod.mk s ⁻¹' A)).toReal with hf
  -- The integrand vanishes outside `[a,b]`.
  have hzero : ∀ s, s ∉ Set.Icc a b → f s = 0 := by
    intro s hs
    have hempty : Prod.mk s ⁻¹' A = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro x hx
      exact hs (hA hx).1
    simp [hf, hempty]
  have hIcc : ∫ s in Set.Icc a b, f s = ∫ s, f s :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs => hzero s hs
  -- `Icc a b` and `Ioc a b` differ by the null set `{a}`.
  have hIoc : ∫ s in Set.Icc a b, f s = ∫ s in Set.Ioc a b, f s := by
    refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero (μ := MeasureTheory.volume)
      measurableSet_Icc.nullMeasurableSet Set.Ioc_subset_Icc_self ?_
    rw [MeasureTheory.ae_iff]
    have hsub : {x : ℝ | ¬(x ∈ Set.Icc a b \ Set.Ioc a b → f x = 0)} ⊆ {a} := by
      intro x hx
      change ¬(x ∈ Set.Icc a b \ Set.Ioc a b → f x = 0) at hx
      have hxmem : x ∈ Set.Icc a b \ Set.Ioc a b := (Classical.not_imp.mp hx).1
      simp only [Set.mem_singleton_iff]
      simp only [Set.mem_sdiff, Set.mem_Icc, Set.mem_Ioc] at hxmem
      obtain ⟨⟨hax, hxb⟩, hnot⟩ := hxmem
      have : ¬ a < x := fun h => hnot ⟨h, hxb⟩
      linarith
    exact MeasureTheory.measure_mono_null hsub Real.volume_singleton
  rw [intervalIntegral.integral_of_le hab]
  exact hIcc.symm.trans hIoc

end Commons.MeasureTheory.Prod