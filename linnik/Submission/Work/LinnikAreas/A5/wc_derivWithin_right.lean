import Mathlib
import Submission.Work.LinnikAreas.A5.Weights
import Submission.Work.LinnikAreas.A5.Basic

open scoped Topology

namespace Work.LinnikAreas.A5

/-- The right within-derivative of the cutoff weight `wc K lam` at the corner `t = K` vanishes.

For `t > K` the cutoff weight is identically zero: `wc K lam t = (sinh (Kλ))⁻¹ * f₁(t)` and
`f₁(t) = sinh((K−t)λ) = 0` for `t ≥ K` (the branch `t ≤ K` is used, and `K - t = 0`).  Hence
`wc K lam` agrees with the constant `0` on a neighbourhood of `K` inside `Set.Ioi K`, and the
within-derivative of a constant is `0`. -/
theorem wc_derivWithin_right (K lam : ℝ) (hK : 0 < K) :
    derivWithin (Work.LinnikAreas.A5.wc K lam) (Set.Ioi K) K = 0 := by
  -- on `Set.Ioi K` the cutoff weight is identically zero
  have heq : (fun _ : ℝ => (0:ℝ)) =ᶠ[𝓝[Set.Ioi K] K] Work.LinnikAreas.A5.wc K lam := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [wc_of_nonneg (le_of_lt (lt_trans hK ht)), f1_of_ge (le_of_lt ht), mul_zero]
  have hx : (0:ℝ) = wc K lam K := by
    rw [wc_of_nonneg hK.le, f1_of_ge le_rfl, mul_zero]
  rw [← heq.derivWithin_eq hx]
  simp

end Work.LinnikAreas.A5
