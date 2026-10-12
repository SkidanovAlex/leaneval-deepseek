import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Submission.Work.BoseFixB3.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB3.CS

/-- The inverse Fourier transform is *defined* as the Bochner integral
`𝓕⁻ f x = ∫ v, 𝐞 ⟪v, x⟫ • f v` (`Real.fourierInv_eq`), and the Bochner integral of a
non-integrable function is `0` (`MeasureTheory.integral_undef`).  So it suffices that the
integrand `v ↦ 𝐞 ⟪v, x⟫ • 𝓕 g v` is not integrable, which follows from
`Real.fourierIntegral_convergent_iff` (multiplication by the unimodular factor
`𝐞 (-⟪v, w⟫)`, here with `w = -x`, preserves integrability).

Concretely: `¬ Integrable (𝓕 g)` ⟹ `¬ Integrable (fun v ↦ 𝐞 ⟪v, x⟫ • 𝓕 g v)` ⟹
`∫ v, 𝐞 ⟪v, x⟫ • 𝓕 g v = 0`. -/
theorem fourierInv_fourier_eq_zero_of_not_integrable
    {g : EuclideanSpace ℝ (Fin 3) → ℂ}
    (h : ¬ MeasureTheory.Integrable (FourierTransform.fourier g) MeasureTheory.volume)
    (x : EuclideanSpace ℝ (Fin 3)) :
    FourierTransformInv.fourierInv (FourierTransform.fourier g) x = 0 := by
  rw [Real.fourierInv_eq]
  apply MeasureTheory.integral_undef
  intro hInt
  refine h ((Real.fourierIntegral_convergent_iff (f := FourierTransform.fourier g) (-x)).mp ?_)
  simpa only [inner_neg_right, neg_neg] using hInt

end Work.BoseFixB3.CS
