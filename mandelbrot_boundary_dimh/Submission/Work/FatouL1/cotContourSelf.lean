import Mathlib
import Submission.Work.FatouL1.solverKernel
import Submission.Work.FatouL1.cotPiNegHalf

/-!
# FATOU-L1: the Cauchy–Heine solver as a cotangent contour integral on its own line

`hcSolver h z = (I/2) * ∫ y, h (z - 1/2 + y*I) * tanh (π y)` is, by the boundary value
`cot (π (-1/2 + i y)) = -i tanh (π y)` of the kernel (`Work.FatouL1.cotPiNegHalf`), exactly `-1/2`
times the *cotangent* contour integral on the line `Re s = Re z - 1/2` (the line on which the
solver is defined):

  `∫ y, h (Re z - 1/2 + y*I) * cot (π (Re z - 1/2 + y*I - z)) = -2 * hcSolver h z`.

On that line `(Re z - 1/2 + y*I) - z = -1/2 + (y - Im z) i`, so the kernel is
`-i tanh (π (y - Im z))`, and the two integrals differ only by the substitution `y ↦ y - Im z`
(`MeasureTheory.integral_add_right_eq_self`).
-/

set_option linter.unnecessarySeqFocus false

open MeasureTheory
open scoped Topology

namespace Work.FatouL1

/-- **The solver as a cotangent integral on its own contour.** -/
theorem cotContourSelf {h : ℂ → ℂ} {z : ℂ}
    (hint : MeasureTheory.Integrable (fun y : ℝ => h (((z.re - 1 / 2 : ℝ) : ℂ) + y * Complex.I))) :
    (∫ y : ℝ, h (((z.re - 1 / 2 : ℝ) : ℂ) + y * Complex.I) *
        Complex.cot (Real.pi * (((z.re - 1 / 2 : ℝ) : ℂ) + y * Complex.I - z))) =
      -2 * Work.FatouL1.hcSolver h z := by
  have _ := hint
  -- write `w` for the real part of the contour and `g` for the shifted integrand of `hcSolver`
  set w : ℂ := ((z.re - 1 / 2 : ℝ) : ℂ) with hw
  set g : ℝ → ℂ := fun u => h (w + (u : ℂ) * Complex.I) *
      ((Real.tanh (Real.pi * (u - z.im))) : ℂ) with hg
  -- the kernel on the contour: `cot (π (w + y I - z)) = -I tanh (π (y - Im z))`
  have harg : ∀ y : ℝ, Real.pi * ((w + (y : ℂ) * Complex.I) - z) =
      Real.pi * ((-1 / 2 : ℂ) + ((y - z.im : ℝ) : ℂ) * Complex.I) := by
    intro y
    rw [hw]; congr 1
    apply Complex.ext <;> simp <;> ring
  have hpt : ∀ y : ℝ, h (w + (y : ℂ) * Complex.I) *
      Complex.cot (Real.pi * ((w + (y : ℂ) * Complex.I) - z)) = -Complex.I * g y := by
    intro y
    rw [harg y, Work.FatouL1.cotPiNegHalf, hg]
    ring
  have hL1 : (∫ y : ℝ, h (w + (y : ℂ) * Complex.I) *
      Complex.cot (Real.pi * ((w + (y : ℂ) * Complex.I) - z))) = ∫ y : ℝ, -Complex.I * g y :=
    integral_congr_ae (Filter.Eventually.of_forall hpt)
  have hL2 : (∫ y : ℝ, -Complex.I * g y) = -Complex.I * ∫ y : ℝ, g y :=
    MeasureTheory.integral_const_mul (-Complex.I) g
  -- `∫ g = ∫ h (z - 1/2 + · I) tanh (π ·)` by the shift `y ↦ y + Im z`
  have harg3 : ∀ y : ℝ, z - 1 / 2 + (y : ℂ) * Complex.I = w + ((y + z.im : ℝ) : ℂ) * Complex.I := by
    intro y
    rw [hw]
    apply Complex.ext <;> simp <;> ring
  have htanh3 : ∀ y : ℝ, Real.tanh (Real.pi * ((y + z.im) - z.im)) = Real.tanh (Real.pi * y) := by
    intro y; congr 2; ring
  have hpt3 : ∀ y : ℝ, h (z - 1 / 2 + (y : ℂ) * Complex.I) *
      ((Real.tanh (Real.pi * y)) : ℂ) = g (y + z.im) := by
    intro y
    simp only [hg]
    rw [harg3 y, htanh3 y]
  have hL3 : (∫ y : ℝ, g y) = ∫ y : ℝ, h (z - 1 / 2 + (y : ℂ) * Complex.I) *
      ((Real.tanh (Real.pi * y)) : ℂ) :=
    (MeasureTheory.integral_add_right_eq_self g z.im).symm.trans
      (integral_congr_ae (Filter.Eventually.of_forall (fun y => (hpt3 y).symm)))
  have hgoal : (∫ y : ℝ, h (w + (y : ℂ) * Complex.I) *
      Complex.cot (Real.pi * ((w + (y : ℂ) * Complex.I) - z))) = -2 * Work.FatouL1.hcSolver h z := by
    rw [hL1, hL2, hL3, Work.FatouL1.hcSolver]
    ring
  simpa [← hw] using hgoal

end Work.FatouL1
