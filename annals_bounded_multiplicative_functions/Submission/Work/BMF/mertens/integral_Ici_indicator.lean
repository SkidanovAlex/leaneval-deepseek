import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mertens

open MeasureTheory intervalIntegral
open scoped Interval

/-- For `a₂ ∈ [a₁, a₃]`, the integral over `[a₁, a₃]` of the function `x ↦ if a₂ ≤ x then g x else 0`
(the indicator of `[a₂, ∞)` times `g`) equals the integral of `g` over `[a₂, a₃]`. -/
theorem integral_Ici_indicator {a₁ a₂ a₃ : ℝ} (h : a₂ ∈ Set.Icc a₁ a₃) {g : ℝ → ℝ} :
    ∫ x in a₁..a₃, (if a₂ ≤ x then g x else 0) = ∫ x in a₂..a₃, g x := by
  obtain ⟨h12, h23⟩ := h
  have h13 : a₁ ≤ a₃ := le_trans h12 h23
  -- Reduce both interval integrals to set integrals over `Ioc`.
  rw [intervalIntegral.integral_of_le h13, intervalIntegral.integral_of_le h23]
  -- Identify the left integrand with the indicator of `Ici a₂`.
  have hfun : (fun x => if a₂ ≤ x then g x else 0) = (Set.Ici a₂).indicator g := by
    funext x
    rw [Set.indicator_apply]
    simp only [Set.mem_Ici]
  rw [hfun]
  rw [MeasureTheory.setIntegral_indicator measurableSet_Ici]
  -- The two sets `Ioc a₁ a₃ ∩ Ici a₂` and `Ioc a₂ a₃` differ only at the point `a₂`.
  have hae : Set.Ioc a₁ a₃ ∩ Set.Ici a₂ =ᵐ[volume] Set.Ioc a₂ a₃ := by
    rw [MeasureTheory.ae_eq_set]
    constructor
    · -- `(Ioc a₁ a₃ ∩ Ici a₂) \ Ioc a₂ a₃ ⊆ {a₂}`.
      apply measure_mono_null _ (measure_singleton a₂)
      intro x hx
      rw [Set.mem_singleton_iff]
      simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici] at hx
      obtain ⟨⟨⟨h1x, hx3⟩, hx2⟩, hnot⟩ := hx
      have hxle : x ≤ a₂ := by
        by_contra hc
        exact hnot ⟨lt_of_not_ge hc, hx3⟩
      exact le_antisymm hxle hx2
    · -- `Ioc a₂ a₃ \ (Ioc a₁ a₃ ∩ Ici a₂) = ∅`.
      have hz : Set.Ioc a₂ a₃ \ (Set.Ioc a₁ a₃ ∩ Set.Ici a₂) = ∅ := by
        rw [Set.sdiff_eq_empty]
        intro x hx
        simp only [Set.mem_Ioc] at hx
        exact ⟨⟨lt_of_le_of_lt h12 hx.1, hx.2⟩, le_of_lt hx.1⟩
      rw [hz]
      simp
  rw [MeasureTheory.setIntegral_congr_set hae]

end Work.BMF.mertens
