import Submission.Work.Fatou.DevH.devH_formula
import Submission.Work.Fatou.DevH.contDiff_devH
import Submission.Work.Fatou.DevH.devHCorr_bounds

/-!
# The quantitative `C¹` property of the interpolating map `devH`

`devH x₀ F ζ = x₀ + ζ + χ(Re ζ)·ε(x₀ + ζ - 1)` interpolates between the translation `ζ ↦ x₀ + ζ`
and `F`.  Its real derivative is within `3/32` of the identity everywhere, it is `C¹`, and its
Wirtinger derivatives are close to `1` and `0`:

`dz devH = 1 + χ'(Re ζ)·ε/2 + χ(Re ζ)·ε'`,  `dzbar devH = χ'(Re ζ)·ε/2`,

where `|χ'| ≤ 2`, `|χ| ≤ 1` and `|ε|, |ε'| ≤ 1/32` on the region where the cut-off does not vanish
(so that all the constants are exactly tight: `2·(1/32) = 1/16`, `(1/32)·1 = 1/32`,
`1/16 + 1/32 = 3/32`).

The ingredients are `hasFDerivAt_devH` (`devH_formula.lean`, the derivative formula),
`devHCorr_bounds` (the estimates on the two coefficients) and `contDiff_devH` (regularity).
-/

namespace Work.Fatou.DevH

open MandelDim Filter Set
open scoped Topology

noncomputable section

/-- `devH` (see `Submission/Work/Fatou/Setup.lean`) is `C¹` and its real derivative is within
`3/32` of the identity everywhere, with the corresponding Wirtinger bounds.  This is the
quantitative heart of the construction: `|ε|, |ε'| ≤ 1/32` on `Q` and `|χ| ≤ 1`, `|χ'| ≤ 2`. -/
theorem devH_deriv {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} (hadm : MandelDim.QAdm b₁ b₂)
    (hF : MandelDim.NearTranslationOn F (MandelDim.Qreg b₁ b₂)) :
    (∀ ζ : ℂ, ‖fderiv ℝ (Work.Fatou.devH (Work.Fatou.xOf b₁ b₂) F) ζ -
        ContinuousLinearMap.id ℝ ℂ‖ ≤ 3 / 32) ∧
    ContDiff ℝ 1 (Work.Fatou.devH (Work.Fatou.xOf b₁ b₂) F) ∧
    (∀ ζ : ℂ, ‖MandelDim.dz (Work.Fatou.devH (Work.Fatou.xOf b₁ b₂) F) ζ - 1‖ ≤ 1 / 16) ∧
    (∀ ζ : ℂ, ‖MandelDim.dzbar (Work.Fatou.devH (Work.Fatou.xOf b₁ b₂) F) ζ‖ ≤ 1 / 32) := by
  have hfderiv : ∀ ζ : ℂ, fderiv ℝ (Work.Fatou.devH (Work.Fatou.xOf b₁ b₂) F) ζ =
      devHDeriv (Work.Fatou.xOf b₁ b₂) F ζ := fun ζ => (hasFDerivAt_devH hadm hF ζ).fderiv
  refine ⟨?_, contDiff_devH hadm hF, ?_, ?_⟩
  · intro ζ
    rw [fderiv_sub_id_eq (hfderiv ζ)]
    exact (devHCorr_bounds hadm hF ζ).1
  · intro ζ
    obtain ⟨-, hc1, hc2⟩ := devHCorr_bounds hadm hF ζ
    exact norm_dz_sub_one_le hc1 hc2 (hfderiv ζ)
  · intro ζ
    obtain ⟨-, hc1, -⟩ := devHCorr_bounds hadm hF ζ
    exact norm_dzbar_le hc1 (hfderiv ζ)

end

end Work.Fatou.DevH
