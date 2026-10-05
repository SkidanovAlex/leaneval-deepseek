import Mathlib

namespace Work.RPCore.Flow

theorem antideriv_eq_self (c : ℝ → ℝ) (hc : ∀ t ∈ Set.Icc (-1 : ℝ) 2, c t = 1) : ∀ t ∈ Set.Icc (-1 : ℝ) 2, (∫ s in (0 : ℝ)..t, c s) = t := by
  intro t ht
  have hcongr : (∫ s in (0 : ℝ)..t, c s) = ∫ s in (0 : ℝ)..t, (1 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro x hx
    apply hc x
    rw [Set.mem_uIcc] at hx
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    · exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  rw [hcongr]
  simp

end Work.RPCore.Flow
