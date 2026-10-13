import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.unusedVariables false

namespace Work.FTS.PhiStar.Honesty

theorem rpow_neg_sub_le {q z h : ℝ} (hq : 0 < q) (hz : 0 < z) (hh : 0 < h) (hhz : h ≤ z) :
    |(z + h) ^ (-q) - z ^ (-q)| ≤ q * z ^ (-q - 1) * h := by
  have hle : z ≤ z + h := by linarith [hhz, hh.le]
  -- the derivative of `x ↦ x ^ (-q)` is dominated by its value at `z` along `[z, z+h]`,
  -- because `x ↦ x ^ (-q-1)` is decreasing on `(0,∞)` when `q > 0`
  have hbound : ∀ x ∈ Set.Icc z (z + h), ‖deriv (fun x : ℝ => x ^ (-q)) x‖ ≤ q * z ^ (-q - 1) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hz hx.1
    rw [Real.deriv_rpow_const, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos hq,
      abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hz hx.1 (by linarith)) hq.le
  have key := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ)
    (s := Set.Icc z (z + h)) (f := fun x : ℝ => x ^ (-q)) (C := q * z ^ (-q - 1))
    (x := z) (y := z + h)
    (fun x hx => Real.differentiableAt_rpow_const_of_ne _ (ne_of_gt (lt_of_lt_of_le hz hx.1)))
    hbound (convex_Icc z (z + h)) ⟨le_refl z, hle⟩ ⟨hle, le_refl (z + h)⟩
  simpa [Real.norm_eq_abs, abs_of_pos hh] using key

end Work.FTS.PhiStar.Honesty
