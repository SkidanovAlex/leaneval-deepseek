import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Submission.Work.BoseFixR.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory
open scoped Real FourierTransform

namespace Work.BoseBogFS

/-- **Continuity of the `p`-convention Fourier transform `Ŵ`.**  For an integrable
`W : ℝ³ → ℝ`, the function `k ↦ Ŵ(k) = ∫ e^{−i⟨k,y⟩}W(y)dy` (`= Work.BoseFixR.chat W k`)
is continuous: it is Mathlib's Fourier transform `𝓕` of the complexification of `W`
(whose continuity for `L¹` data is `VectorFourier.fourierIntegral_continuous`) composed
with the contraction `k ↦ (2π)⁻¹ • k`, and then the real part. -/
theorem continuous_chat (W : EuclideanSpace ℝ (Fin 3) → ℝ) (hW : MeasureTheory.Integrable W) :
    Continuous (Work.BoseFixR.chat W) := by
  have hf : MeasureTheory.Integrable (fun y : EuclideanSpace ℝ (Fin 3) => ((W y : ℝ) : ℂ)) :=
    hW.ofReal
  have hF : Continuous (𝓕 (fun y : EuclideanSpace ℝ (Fin 3) => ((W y : ℝ) : ℂ))) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hf
  have hcomp : Continuous (fun k : EuclideanSpace ℝ (Fin 3) =>
      (𝓕 (fun y : EuclideanSpace ℝ (Fin 3) => ((W y : ℝ) : ℂ))) ((2 * Real.pi)⁻¹ • k)) :=
    hF.comp (continuous_const_smul ((2 * Real.pi)⁻¹))
  have key : Work.BoseFixR.chat W
      = fun k : EuclideanSpace ℝ (Fin 3) =>
          (𝓕 (fun y : EuclideanSpace ℝ (Fin 3) => ((W y : ℝ) : ℂ))
            ((2 * Real.pi)⁻¹ • k)).re := by
    funext k
    simp only [Work.BoseFixR.chat]
    rw [Work.SmallBoxBridge.Resolve.kinFT_eq_fourier]
  rw [key]
  exact Complex.continuous_re.comp hcomp

end Work.BoseBogFS
