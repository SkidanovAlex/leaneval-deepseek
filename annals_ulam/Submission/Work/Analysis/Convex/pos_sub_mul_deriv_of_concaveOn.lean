import Mathlib

namespace Work.Analysis.Convex

/-- For a concave, differentiable function `f` on `(-1, 1)` with `f 0 = 1`, one has
`0 < f t - t * deriv f t` at every point `t` of the interval.

The proof is the tangent-line (sub-gradient) inequality for concave functions: a concave
differentiable function lies below its tangent line at every interior point, so
`f 0 ≤ f t + deriv f t * (0 - t) = f t - t * deriv f t`; since `f 0 = 1` the quantity is at
least `1`.  The tangent inequality in the two directions is furnished by
`ConcaveOn.slope_le_deriv` (for `t < 0`) and `ConcaveOn.deriv_le_slope` (for `t > 0`), which
compare the derivative at an endpoint of a secant with that secant's slope. -/
theorem pos_sub_mul_deriv_of_concaveOn {f : ℝ → ℝ} (hf0 : f 0 = 1)
    (hconc : ConcaveOn ℝ (Set.Ioo (-1 : ℝ) 1) f)
    (hdiff : DifferentiableOn ℝ f (Set.Ioo (-1 : ℝ) 1)) {t : ℝ}
    (ht : t ∈ Set.Ioo (-1 : ℝ) 1) : 0 < f t - t * deriv f t := by
  have h0 : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := by constructor <;> norm_num
  rcases lt_trichotomy t 0 with htlt | heq | htgt
  · -- `t < 0`: the slope of the secant from `t` to `0` is bounded above by `deriv f t`.
    have hdt : DifferentiableAt ℝ f t := hdiff.differentiableAt (isOpen_Ioo.mem_nhds ht)
    have hs := hconc.slope_le_deriv ht h0 htlt hdt
    rw [slope_def_field, hf0] at hs
    have hneg : (0 : ℝ) - t = -t := by ring
    rw [hneg] at hs
    have hpos : 0 < -t := by linarith
    have h := (div_le_iff₀ hpos).mp hs
    nlinarith
  · -- `t = 0`: immediate from `f 0 = 1`.
    subst heq
    simp [hf0]
  · -- `0 < t`: the slope of the secant from `0` to `t` is bounded below by `deriv f t`.
    have hdt : DifferentiableAt ℝ f t := hdiff.differentiableAt (isOpen_Ioo.mem_nhds ht)
    have hs := hconc.deriv_le_slope h0 ht htgt hdt
    rw [slope_def_field, hf0] at hs
    have hz : t - (0 : ℝ) = t := by ring
    rw [hz] at hs
    have hpos : 0 < t := htgt
    have h := (le_div_iff₀ hpos).mp hs
    nlinarith

end Work.Analysis.Convex
