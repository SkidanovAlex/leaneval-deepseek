import Mathlib
import Submission.Work.RPB.Defs

/-!
# The parallelogram identity for the signed area (node B5 of the rectangular-peg route)

The signed area `signedArea c = (1/2) ∮ ω_ℂ(c, c')` is the quadratic form associated with the
(skew) bilinear area form `ω_ℂ a b = Im(conj a · b)`.  For any two curves `α`, `β` the
polarisation identity of a quadratic form therefore reads

`signedArea (α + β) + signedArea (α - β) = 2 · signedArea α + 2 · signedArea β`,

exactly as for the square of a norm.  This is what the node needs in order to recognise a sum of
signed areas of glued curves as a combination of the two summands.

The proof is completely pointwise.  Expanding `ω_ℂ` in the real coordinates of `ℂ` gives

`ω_ℂ (x+y) (u+v) + ω_ℂ (x-y) (u-v) = 2 ω_ℂ x u + 2 ω_ℂ y v`

(`omegaC_parallelogram`), an identity of real bilinear forms.  Feeding `x = α t`, `y = β t`,
`u = (α+β)' t`, `v = (α-β)' t` and using `deriv` of a sum and a difference — legitimate because
`ContDiff ℝ 1` makes both curves differentiable — turns the two signed areas into a single
integrand identity.  The integral of the sum is the sum of the integrals since every integrand is
continuous (`ω_ℂ` is a continuous function of its two arguments, and `ContDiff ℝ 1` gives
continuity of the curve and of its derivative), so all the required `IntervalIntegrable`
hypotheses come from `Continuous.intervalIntegrable`.  Finally the factor `1/2` is distributed.
-/

open RectangularPegProblem
open Manifold Complex Real
open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

open Work.RPV

/-- `ω_ℂ` is continuous as a function of the pair of its arguments. -/
lemma continuous_omegaC_pair : Continuous (fun p : ℂ × ℂ => ωC p.1 p.2) := by
  simp only [ωC]
  continuity

/-- **The parallelogram identity for the area form `ω_ℂ`.**
`ω_ℂ` is a real bilinear form (its coordinate form is `u.re * v.im - u.im * v.re`), so the same
algebraic identity as for the square of a norm holds:
`ω_ℂ (x+y) (u+v) + ω_ℂ (x-y) (u-v) = 2 ω_ℂ x u + 2 ω_ℂ y v`. -/
lemma omegaC_parallelogram (x y u v : ℂ) :
    ωC (x + y) (u + v) + ωC (x - y) (u - v) = 2 * ωC x u + 2 * ωC y v := by
  simp only [ωC, map_add, map_sub, Complex.add_im, Complex.sub_im, Complex.mul_im,
    Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.add_re, Complex.sub_re]
  ring

/-- **The signed area is a quadratic form: the parallelogram identity.**
For `C¹` plane curves `α` and `β`,
`signedArea (α + β) + signedArea (α - β) = 2 · signedArea α + 2 · signedArea β`. -/
theorem signedArea_parallelogram (α β : ℝ → ℂ) (hα : ContDiff ℝ 1 α) (hβ : ContDiff ℝ 1 β) :
    Work.RPB.signedArea (fun t => α t + β t) + Work.RPB.signedArea (fun t => α t - β t)
      = 2 * Work.RPB.signedArea α + 2 * Work.RPB.signedArea β := by
  have hdα : Differentiable ℝ α := hα.differentiable (by norm_num)
  have hdβ : Differentiable ℝ β := hβ.differentiable (by norm_num)
  have hctα : Continuous α := hα.continuous
  have hctβ : Continuous β := hβ.continuous
  have hcdα : Continuous (deriv α) := hα.continuous_deriv_one
  have hcdβ : Continuous (deriv β) := hβ.continuous_deriv_one
  -- derivative of a sum and of a difference
  have hda : ∀ t, deriv (fun s => α s + β s) t = deriv α t + deriv β t :=
    fun t => deriv_add (hdα t) (hdβ t)
  have hds : ∀ t, deriv (fun s => α s - β s) t = deriv α t - deriv β t :=
    fun t => deriv_sub (hdα t) (hdβ t)
  -- the integrands are continuous, hence interval integrable
  have hcont1 : Continuous (fun t => ωC (α t + β t) (deriv α t + deriv β t)) := by
    continuity
  have hcont2 : Continuous (fun t => ωC (α t - β t) (deriv α t - deriv β t)) := by
    continuity
  have hint1 : IntervalIntegrable (fun t => ωC (α t + β t) (deriv α t + deriv β t))
      MeasureTheory.volume 0 (2 * Real.pi) := hcont1.intervalIntegrable 0 (2 * Real.pi)
  have hint2 : IntervalIntegrable (fun t => ωC (α t - β t) (deriv α t - deriv β t))
      MeasureTheory.volume 0 (2 * Real.pi) := hcont2.intervalIntegrable 0 (2 * Real.pi)
  have hcontL : Continuous (fun t => ωC (α t) (deriv α t)) := by
    continuity
  have hcontM : Continuous (fun t => ωC (β t) (deriv β t)) := by
    continuity
  have hintL : IntervalIntegrable (fun t => ωC (α t) (deriv α t)) MeasureTheory.volume 0 (2 * Real.pi) :=
    hcontL.intervalIntegrable 0 (2 * Real.pi)
  have hintM : IntervalIntegrable (fun t => ωC (β t) (deriv β t)) MeasureTheory.volume 0 (2 * Real.pi) :=
    hcontM.intervalIntegrable 0 (2 * Real.pi)
  -- replace the derivative of the sum (resp. difference) by the sum (resp. difference) of the
  -- derivatives, under the integral sign
  have hI1 : (∫ t in (0 : ℝ)..(2 * Real.pi), ωC (α t + β t) (deriv (fun s => α s + β s) t))
      = ∫ t in (0 : ℝ)..(2 * Real.pi), ωC (α t + β t) (deriv α t + deriv β t) := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only []
    rw [hda t]
  have hI2 : (∫ t in (0 : ℝ)..(2 * Real.pi), ωC (α t - β t) (deriv (fun s => α s - β s) t))
      = ∫ t in (0 : ℝ)..(2 * Real.pi), ωC (α t - β t) (deriv α t - deriv β t) := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only []
    rw [hds t]
  -- the pointwise parallelogram identity passes to the integrals
  have hA : (∫ t in (0 : ℝ)..(2 * Real.pi),
        (ωC (α t + β t) (deriv α t + deriv β t) + ωC (α t - β t) (deriv α t - deriv β t)))
      = ∫ t in (0 : ℝ)..(2 * Real.pi),
        (2 * ωC (α t) (deriv α t) + 2 * ωC (β t) (deriv β t)) := by
    apply intervalIntegral.integral_congr
    intro t _
    exact omegaC_parallelogram (α t) (β t) (deriv α t) (deriv β t)
  have hB : (∫ t in (0 : ℝ)..(2 * Real.pi),
        (2 * ωC (α t) (deriv α t) + 2 * ωC (β t) (deriv β t)))
      = 2 * (∫ t in (0 : ℝ)..(2 * Real.pi), ωC (α t) (deriv α t))
        + 2 * (∫ t in (0 : ℝ)..(2 * Real.pi), ωC (β t) (deriv β t)) := by
    rw [intervalIntegral.integral_add (hintL.const_mul 2) (hintM.const_mul 2),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hsum : (∫ t in (0 : ℝ)..(2 * Real.pi), ωC (α t + β t) (deriv α t + deriv β t))
        + (∫ t in (0 : ℝ)..(2 * Real.pi), ωC (α t - β t) (deriv α t - deriv β t))
      = 2 * (∫ t in (0 : ℝ)..(2 * Real.pi), ωC (α t) (deriv α t))
        + 2 * (∫ t in (0 : ℝ)..(2 * Real.pi), ωC (β t) (deriv β t)) := by
    rw [← intervalIntegral.integral_add hint1 hint2, hA, hB]
  -- assemble
  have hmain : (∫ t in (0 : ℝ)..(2 * Real.pi), ωC (α t + β t) (deriv (fun s => α s + β s) t))
        + (∫ t in (0 : ℝ)..(2 * Real.pi), ωC (α t - β t) (deriv (fun s => α s - β s) t))
      = 2 * (∫ t in (0 : ℝ)..(2 * Real.pi), ωC (α t) (deriv α t))
        + 2 * (∫ t in (0 : ℝ)..(2 * Real.pi), ωC (β t) (deriv β t)) := by
    rw [hI1, hI2]
    exact hsum
  simp only [Work.RPB.signedArea]
  linear_combination (1 / 2) * hmain

end Work.RPB.B5
