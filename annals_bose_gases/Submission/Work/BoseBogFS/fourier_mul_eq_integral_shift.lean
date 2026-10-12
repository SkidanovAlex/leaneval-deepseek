import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Submission.Work.BoseFixR.LatGreen.RadialSmoothCosDecaySchwartz
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory
open scoped Real FourierTransform

namespace Work.BoseBogFS

/-- **The Fubini/Parseval step for a product with a Fourier-inversion representation** (complex-`L¹`
companion of `Work.BoseFixR.LatGreen.fubini_mul_fourierChar`, which is in
`Submission.Work.BoseFixR.LatGreen.RadialSmoothCosDecaySchwartz`): if `G` is integrable and
`B x = ∫ η, 𝐞⟪η,x⟫ • G η` pointwise, then the Fourier transform of the product `A · B` is the
`G`-superposition of the shifted Fourier transforms of `A`:
  `𝓕 (A · B) ν = ∫ η, G η * 𝓕 A (ν - η)`.
Hints: everything is public. `Real.fourier_eq (fun x => A x * B x) ν` rewrites the LHS as
`∫ x, 𝐞 (-⟪x,ν⟫) • (A x * B x)`; `integral_congr_ae` + `Circle.smul_def` + `smul_eq_mul` +
`real_inner_comm` and `ring` turn the integrand into the term
`A x * B x * ↑(𝐞 (-⟪ν, x⟫))`.  Then
`Work.BoseFixR.LatGreen.fubini_mul_fourierChar (W := A) (Ψ := B) (G := G) hA hG hB ν`
(stated for `W Ψ G : EuclideanSpace ℝ (Fin 3) → ℂ`, hypothesis
`hΨ : ∀ x, Ψ x = ∫ η, 𝐞 (inner ℝ η x) • G η`, conclusion
`∫ x, W x * Ψ x * ↑(𝐞 (-inner ℝ ν x)) = ∫ η, G η * 𝓕 W (ν - η)`) finishes.  Note the `𝐞`
notation is `Real.fourierChar` (`open scoped Real FourierTransform` in your file), so
`Real.fourierChar (inner ℝ η x) • G η` (the form written here) and `𝐞 (inner ℝ η x) • G η` are
definitionally equal.  Add `open MeasureTheory` for the `Integrable`/Fourier API. -/
theorem fourier_mul_eq_integral_shift {A B G : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hA : MeasureTheory.Integrable A) (hG : MeasureTheory.Integrable G)
    (hB : ∀ x : EuclideanSpace ℝ (Fin 3),
      B x = ∫ η : EuclideanSpace ℝ (Fin 3), Real.fourierChar (inner ℝ η x) • G η)
    (ν : EuclideanSpace ℝ (Fin 3)) :
    FourierTransform.fourier (fun x : EuclideanSpace ℝ (Fin 3) => A x * B x) ν
      = ∫ η : EuclideanSpace ℝ (Fin 3), G η * FourierTransform.fourier A (ν - η) := by
  rw [Real.fourier_eq]
  -- The LHS integrand `𝐞(-⟪x,ν⟫) • (A x * B x)` is the term `A x * B x * ↑(𝐞(-⟪ν,x⟫))`
  -- handled by `fubini_mul_fourierChar`.
  have h1 : (∫ x : EuclideanSpace ℝ (Fin 3), 𝐞 (-(inner ℝ x ν)) • (A x * B x))
      = ∫ x : EuclideanSpace ℝ (Fin 3), A x * B x * ↑(𝐞 (-(inner ℝ ν x))) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show 𝐞 (-(inner ℝ x ν)) • (A x * B x) = A x * B x * ↑(𝐞 (-(inner ℝ ν x)))
    rw [Circle.smul_def, smul_eq_mul, real_inner_comm x ν]
    ring
  rw [h1]
  exact Work.BoseFixR.LatGreen.fubini_mul_fourierChar hA hG hB ν

end Work.BoseBogFS
