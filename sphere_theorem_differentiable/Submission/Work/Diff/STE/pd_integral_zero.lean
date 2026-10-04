import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.CubeSplit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The integral of a periodic partial derivative vanishes

For a function `h : (ι → ℝ) → ℂ` that is `C¹` and `1`-periodic in the coordinate `i`, the
`i`-th partial derivative `pd i h`, evaluated along the line `t ↦ insertAt i t y`, integrates to
`0` over a full period `[0,1]`:

`∫ t in 0..1, pd i h (insertAt i t y) = 0`.

This is the fundamental theorem of calculus: the map `t ↦ h (insertAt i t y)` is `C¹` with
derivative `t ↦ pd i h (insertAt i t y)`, and it is `1`-periodic, so the endpoint values cancel.
It is Layer A's "periodic integration by parts" (`∫ ∂ᵢ f = 0`) of the STE design.
-/

noncomputable section

namespace Work.Diff.STE

open MeasureTheory BigOperators
open scoped ComplexConjugate ContDiff

theorem pd_integral_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (h : (ι → ℝ) → ℂ)
    (hh : ContDiff ℝ 1 h) (hper : PeriodicIn i h) (y : {j : ι // j ≠ i} → ℝ) :
    ∫ t in (0 : ℝ)..1, pd i h (insertAt i t y) = 0 := by
  -- The line `t ↦ insertAt i t y` is C¹ with derivative `eᵢ`; composing with `h` gives the
  -- derivative of the periodised curve.
  have hderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => h (insertAt i s y))
      (pd i h (insertAt i t y)) t := by
    intro t
    have hdiff : Differentiable ℝ h := hh.differentiable (by norm_num)
    have h1 := (hdiff (insertAt i t y)).hasFDerivAt
    have h2 := h1.comp_hasDerivAt t (hasDerivAt_insertAt i y t)
    have h3 : HasDerivAt (fun s : ℝ => h (insertAt i s y))
        ((fderiv ℝ h (insertAt i t y)) (Pi.single i 1)) t := h2
    simpa [pd] using h3
  -- The integrand is continuous: `pd i h` is the composition of the continuous `fderiv ℝ h`
  -- with the evaluation at `eᵢ`.
  have hint : IntervalIntegrable (fun t : ℝ => pd i h (insertAt i t y)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    have hcont' : Continuous fun x : ι → ℝ => pd i h x := by
      simp only [pd]
      exact (hh.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hci : Continuous fun t : ℝ => insertAt i t y := by
      have : (fun t : ℝ => insertAt i t y)
          = fun t : ℝ => insertAt i 0 y + t • (Pi.single i 1 : ι → ℝ) := by
        funext s; simpa using insertAt_add i 0 s y
      rw [this]
      exact (continuous_id.smul continuous_const).const_add _
    exact hcont'.comp hci
  -- Periodicity of the curve makes the endpoint values equal.
  have hper1 : (fun s : ℝ => h (insertAt i s y)) 1
      = (fun s : ℝ => h (insertAt i s y)) 0 := by
    show h (insertAt i 1 y) = h (insertAt i 0 y)
    rw [insertAt_one_eq_insertAt_zero_add]
    exact hper (insertAt i 0 y)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t) hint]
  exact sub_eq_zero.mpr hper1

end Work.Diff.STE
