import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

namespace Commons.Analysis.Fourier

/-- A Schwartz function's inverse Fourier transform is integrable. -/
theorem integrable_fourierInv_schwartzMap (F : SchwartzMap ℝ ℂ) :
    MeasureTheory.Integrable (FourierTransform.fourierInv (F : ℝ → ℂ)) := by
  rw [← SchwartzMap.fourierInv_coe F]
  exact SchwartzMap.integrable (FourierTransform.fourierInv F)

theorem integrable_fourierInv_of_contDiff_hasCompactSupport {f : ℝ → ℂ} (hf : HasCompactSupport f)
    (hs : ContDiff ℝ (⊤ : ℕ∞) f) :
    MeasureTheory.Integrable (FourierTransform.fourierInv f) := by
  have hcoe : ((hf.toSchwartzMap hs : SchwartzMap ℝ ℂ) : ℝ → ℂ) = f := by
    funext x
    rw [HasCompactSupport.toSchwartzMap_toFun]
  rw [← hcoe]
  exact integrable_fourierInv_schwartzMap (hf.toSchwartzMap hs)

end Commons.Analysis.Fourier