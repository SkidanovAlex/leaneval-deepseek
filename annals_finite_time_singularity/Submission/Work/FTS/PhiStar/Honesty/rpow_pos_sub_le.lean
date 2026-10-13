import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

/-- The mean-value bound for the increasing, convex function `x ↦ x ^ p` (`p ≥ 1`) on the
half-line: for `0 < z` and `0 < h ≤ z`, the increment over `[z, z + h]` is at most the
endpoint derivative `p (2z)^{p-1}` times the step `h`.  Formally, `(z + h) ^ p - z ^ p =
p · c ^ (p - 1) · h` for some `c ∈ (z, z + h)` (mean value theorem), and `c ≤ z + h ≤ 2 z`
together with `p - 1 ≥ 0` bounds `p c ^ (p - 1)` by `p (2z) ^ (p - 1)`. -/
theorem rpow_pos_sub_le {p z h : ℝ} (hp : 1 ≤ p) (hz : 0 < z) (hh : 0 < h) (hhz : h ≤ z) :
    |(z + h) ^ p - z ^ p| ≤ p * (2 * z) ^ (p - 1) * h := by
  have hzh : z ≤ z + h := by linarith
  -- the mean value theorem on `[z, z + h]` with the endpoint derivative bound
  have hbound := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := fun x : ℝ => x ^ p) (f' := fun x : ℝ => p * x ^ (p - 1))
      (a := z) (b := z + h) (C := p * (2 * z) ^ (p - 1))
      (by
        intro x hx
        exact (Real.hasDerivAt_rpow_const
          (Or.inl (by linarith [hx.1, hz] : x ≠ 0))).hasDerivWithinAt)
      (by
        intro x hx
        have hx0 : 0 < x := lt_of_lt_of_le hz hx.1
        have hx2z : x ≤ 2 * z := by linarith [hx.2, hhz]
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hx0.le hx2z (by linarith)) (by linarith))
      (z + h) ⟨hzh, le_rfl⟩
  simpa using hbound

end Work.FTS.PhiStar.Honesty
