import Mathlib.Tactic.Have
import Mathlib.Analysis.Fourier.Convolution
import Submission.Work.OneBodyKin.kinFT_chi_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.OneBodyKin.kinFT_conv3_chi`

The convolution theorem for the `p`-convention Fourier transform `kinFT` at the bump `χ`:

    `kinFT (χ ⋆ χ) p = (profHat p)²`,

where `conv3` is the unnormalised Lebesgue convolution `(f ⋆ g)(x) = ∫ y, f y · g (x − y)`
and `profHat p = ∫_z χ z · cos⟪p,z⟫ dz` is the real cosine profile of `χ` (equal to the
Fourier transform of `χ` by `kinFT_chi_eq`).

The proof is the standard convolution theorem, with no `(2π)`-normalisation: `kinFT` is
Mathlib's `𝓕` at the frequency `(2π)⁻¹ • p` (`Work.SmallBoxBridge.Resolve.kinFT_eq_fourier`),
`conv3` is Mathlib's convolution `⋆[ContinuousLinearMap.mul ℂ ℂ]` after complexification, and
`Real.fourier_mul_convolution_eq` turns the Fourier transform of a convolution into the
product of the Fourier transforms.  Folded back through `kinFT_chi_eq` this gives
`(profHat p)²`.
-/

noncomputable section

open MeasureTheory
open scoped Convolution

namespace Work.OneBodyKin

open Submission.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 800000

theorem kinFT_conv3_chi (p : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.kinFT
        (fun w : EuclideanSpace ℝ (Fin 3) =>
          ((Submission.BoseGases.conv3 Submission.BoseGases.chi
            Submission.BoseGases.chi w : ℝ) : ℂ)) p
      = (Work.OneBodyKin.profHat p : ℂ) ^ 2 := by
  -- `χ : ℝ³ → ℂ` is integrable (continuous, compactly supported)
  have hχ : Integrable (fun y : ℝ³ => (chi y : ℂ)) :=
    Complex.ofRealCLM.integrable_comp
      (chi_continuous.integrable_of_hasCompactSupport chi_hasCompactSupport)
  -- the complexification of `conv3 χ χ` is the convolution of `χ` with itself
  have hconv : (fun w : ℝ³ => ((conv3 chi chi w : ℝ) : ℂ))
      = (fun y : ℝ³ => (chi y : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ]
          (fun y : ℝ³ => (chi y : ℂ)) := by
    funext x
    rw [convolution_mul]
    simp only [conv3]
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (ae_of_all _ (fun t => ?_))
    simp only [Complex.ofReal_mul]
  rw [hconv, Work.SmallBoxBridge.Resolve.kinFT_eq_fourier,
    Real.fourier_mul_convolution_eq hχ hχ]
  rw [← Work.SmallBoxBridge.Resolve.kinFT_eq_fourier, kinFT_chi_eq]
  ring

end Work.OneBodyKin
