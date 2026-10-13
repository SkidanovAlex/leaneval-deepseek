import Mathlib

namespace Work.WilE2

/-- **Sard's lemma in the square case.**  For a map `f : ℝⁿ → ℝⁿ` which is differentiable
everywhere (with derivative `f'`), the image of the set of points where the differential is
singular is Lebesgue-null.

This is Mathlib's `MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`
(a proof of Sard's lemma in fixed dimension, following Fremlin), applied to the set
`{x | (f' x).det = 0}`: on that set `f` is differentiable within the set with derivative `f'`
by `HasFDerivAt.hasFDerivWithinAt`, and by definition the determinant of the derivative vanishes
there. -/
theorem sard_square {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ)) (f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (hf' : ∀ x, HasFDerivAt f (f' x) x) : MeasureTheory.volume (f '' {x | (f' x).det = 0}) = 0 := MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero MeasureTheory.volume (fun x _ => (hf' x).hasFDerivWithinAt) (fun _ hx => hx)

end Work.WilE2
