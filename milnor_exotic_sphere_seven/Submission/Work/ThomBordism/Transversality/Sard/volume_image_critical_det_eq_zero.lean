import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The equidimensional case of Sard's theorem

The image of the critical set of a differentiable endomorphism of `ℝⁿ` — the set of points at which
the derivative is singular — is Lebesgue-null.  This is Mathlib's
`MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero` ("a version of Sard's lemma in
fixed dimension"), instantiated at `s = univ` and `f' = fderiv ℝ f`.
-/

namespace Work.ThomBordism.Transversality.Sard

/-- **Sard's theorem, equidimensional case**: the image of the set of points at which the derivative
of a differentiable map `ℝⁿ → ℝⁿ` is singular has measure zero. -/
theorem volume_image_critical_det_eq_zero {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hf : Differentiable ℝ f) :
    MeasureTheory.volume (f '' {x | (fderiv ℝ f x).det = 0}) = 0 := by
  refine MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero
    (MeasureTheory.volume) (f := f) (f' := fun x => fderiv ℝ f x) ?_ ?_
  · intro x _
    exact (hf x).hasFDerivAt.hasFDerivWithinAt
  · intro x hx
    exact hx

end Work.ThomBordism.Transversality.Sard
