import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Derivative of `x ↦ c * cot (c * x)`

Mathlib (at this pin) has no derivative lemma for `Real.cot`, so we prove one here and
then derive the scaled version used by the Riccati / index-form comparison in
`Submission.Work.Diff.C` (the `Hess d` bounds).

Recall `Real.cot x = cos x / sin x`, so for `sin x ≠ 0`

  `deriv cot x = (-sin x * sin x - cos x * cos x) / sin x ^ 2
               = -1 / sin x ^ 2 = -(1 + cot x ^ 2)`.

Differentiating `s ↦ c * cot (c * s)` with the chain rule multiplies this by `c ^ 2`, and
`c ^ 2 * (1 + cot (c*t) ^ 2) = c ^ 2 + (c * cot (c*t)) ^ 2`.
-/

namespace Work.Diff.C

/-- Mathlib has no `HasDerivAt` lemma for `Real.cot`; this is the basic one.
`deriv cot = -(1 + cot ^ 2)` away from the zeros of `sin`. -/
theorem hasDerivAt_cot {x : ℝ} (h : Real.sin x ≠ 0) :
    HasDerivAt Real.cot (-(1 + Real.cot x ^ 2)) x := by
  have hcot_eq : Real.cot = fun y : ℝ => Real.cos y / Real.sin y :=
    funext Real.cot_eq_cos_div_sin
  rw [hcot_eq]
  have hdiv : HasDerivAt (fun y : ℝ => Real.cos y / Real.sin y)
      ((-Real.sin x * Real.sin x - Real.cos x * Real.cos x) / Real.sin x ^ 2) x :=
    (Real.hasDerivAt_cos x).div (Real.hasDerivAt_sin x) h
  convert hdiv using 1
  change -(1 + (Real.cos x / Real.sin x) ^ 2) =
    (-Real.sin x * Real.sin x - Real.cos x * Real.cos x) / Real.sin x ^ 2
  field_simp
  ring

/-- Derivative of the scaled cotangent `s ↦ c * cot (c * s)`. -/
theorem hasDerivAt_cot_const_mul {c t : ℝ} (h : Real.sin (c * t) ≠ 0) :
    HasDerivAt (fun s : ℝ => c * Real.cot (c * s)) (-(c ^ 2 + (c * Real.cot (c * t)) ^ 2)) t := by
  have hcot : HasDerivAt Real.cot (-(1 + Real.cot (c * t) ^ 2)) (c * t) :=
    hasDerivAt_cot h
  have hinner : HasDerivAt (fun s : ℝ => c * s) c t := by
    simpa using (hasDerivAt_id t).const_mul c
  have hcomp : HasDerivAt (fun s : ℝ => Real.cot (c * s))
      ((-(1 + Real.cot (c * t) ^ 2)) * c) t :=
    hcot.comp t hinner
  have hres := hcomp.const_mul c
  convert hres using 1
  ring

end Work.Diff.C
