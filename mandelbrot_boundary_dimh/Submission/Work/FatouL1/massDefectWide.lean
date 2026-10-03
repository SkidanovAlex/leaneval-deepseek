import Mathlib
import Submission.Work.FatouL1.massFatouDerivSubInv
import Submission.Work.FatouL1.massFatouDerivSubInvWide
import Submission.Work.FatouL1.massFatouDerivSubInv_wide
import Submission.Work.FatouL1.mass_fatouDerivError

namespace Work.FatouL1

/-- **The line mass of the defect `Φ' - 1/(F - id)` is finite, uniformly, on the wide strip
`x₀ - 1 < Re < x₀ + 3`.**

This is the union of the two strips already covered in the area:
`Work.FatouL1.mass_fatouDerivError` (the Strip `x₀ - 1 < Re < x₀ + 14/5`) and
`Work.FatouL1.massFatouDerivSubInv_wide` (the strip `x₀ - 3/4 < Re < x₀ + 3`); note
`14/5 > -3/4`, so every point of `(x₀ - 1, x₀ + 3)` lies in one of the two.  Taking the maximum
of the two bounds gives a single constant. -/
theorem massDefectWide {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} {x₀ : ℝ}
    (hadm : MandelDim.QAdm b₁ b₂) (hF : MandelDim.NearTranslationL1 F (MandelDim.Qreg b₁ b₂))
    (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀) (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re)
    {Φ : ℂ → ℂ} (hΦ : MandelDim.IsFatouCoordOn F Φ (MandelDim.Qreg b₁ b₂)) :
    ∃ m : ℝ, ∀ x ∈ Set.Ioo (x₀ - 1) (x₀ + 3),
      ∫⁻ y : ℝ, ENNReal.ofReal
        ‖deriv Φ ((x : ℂ) + y * Complex.I) -
          (F ((x : ℂ) + y * Complex.I) - ((x : ℂ) + y * Complex.I))⁻¹‖ ≤ ENNReal.ofReal m := by
  obtain ⟨m₁, hm₁⟩ :=
    mass_fatouDerivError hadm hF h₁ h₂ hΦ Work.FatouCH.fatouDerivEstimate
  obtain ⟨m₂, hm₂⟩ := massFatouDerivSubInv_wide hadm hF h₁ h₂ hΦ
  refine ⟨max m₁ m₂, fun x hx => ?_⟩
  rcases lt_or_ge x (x₀ + 14 / 5) with hlt | hge
  · exact le_trans (hm₁ x ⟨hx.1, hlt⟩) (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  · refine le_trans (hm₂ x ⟨?_, hx.2⟩) (ENNReal.ofReal_le_ofReal (le_max_right _ _))
    linarith

end Work.FatouL1
