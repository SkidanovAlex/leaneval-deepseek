import Mathlib
import Submission.Work.LinnikAreas.A5.Weights
import Submission.Work.LinnikAreas.A5.Basic

open Complex DirichletCharacter Metric Filter
open scoped Interval Topology BigOperators

namespace Work.LinnikAreas.A5

/-- Left derivative at `t = K` of the cut-off test function `wc K lam`.

Near `K` (from the left) `wc K lam` agrees with the smooth branch
`t ↦ (sinh (Kλ))⁻¹ · sinh((K−t)λ)`, whose value at `K` is `1` and whose derivative is
`(sinh (Kλ))⁻¹ · cosh 0 · (−λ) = −(sinh (Kλ))⁻¹ · λ`.
This is the `t = K` endpoint value used, e.g., when integrating by parts the Laplace
transform `Ftil K lam`. -/
theorem wc_derivWithin_left (K lam : ℝ) (hK : 0 < K) :
    derivWithin (Work.LinnikAreas.A5.wc K lam) (Set.Iio K) K
      = -(Real.sinh (K * lam))⁻¹ * lam := by
  -- The smooth branch `F t = (sinh (Kλ))⁻¹ · sinh((K−t)λ)` has derivative `−(sinh (Kλ))⁻¹ λ` at `K`.
  have hF : HasDerivAt (fun t : ℝ => (Real.sinh (K * lam))⁻¹ * Real.sinh ((K - t) * lam))
      (-(Real.sinh (K * lam))⁻¹ * lam) K := by
    have h1 : HasDerivAt (fun t : ℝ => (K - t) * lam) (-lam) K := by
      have hsub : HasDerivAt (fun t : ℝ => K - t) (-1) K := (hasDerivAt_id K).const_sub K
      have := hsub.mul_const lam
      simpa using this
    have h2 : HasDerivAt (fun t : ℝ => Real.sinh ((K - t) * lam))
        (Real.cosh ((K - K) * lam) * (-lam)) K := h1.sinh
    have h3 := h2.const_mul ((Real.sinh (K * lam))⁻¹)
    have hval : (Real.sinh (K * lam))⁻¹ * (Real.cosh ((K - K) * lam) * (-lam))
        = -(Real.sinh (K * lam))⁻¹ * lam := by
      rw [sub_self, zero_mul, Real.cosh_zero, one_mul]; ring
    rw [hval] at h3
    exact h3
  -- `wc K lam` agrees with the smooth branch on `Iio K` close to `K` (where `t > 0`).
  have heq : wc K lam =ᶠ[𝓝[Set.Iio K] K]
      (fun t => (Real.sinh (K * lam))⁻¹ * Real.sinh ((K - t) * lam)) := by
    rw [Filter.EventuallyEq, eventually_nhdsWithin_iff]
    filter_upwards [isOpen_Ioi.mem_nhds hK] with t ht hts
    rw [wc_of_nonneg (le_of_lt ht), f1_of_le (le_of_lt hts)]
  have hx : wc K lam K = (Real.sinh (K * lam))⁻¹ * Real.sinh ((K - K) * lam) := by
    rw [wc_of_nonneg hK.le, f1_of_le le_rfl]
  have hwd : HasDerivWithinAt (wc K lam) (-(Real.sinh (K * lam))⁻¹ * lam) (Set.Iio K) K :=
    hF.hasDerivWithinAt.congr_of_eventuallyEq heq hx
  exact hwd.derivWithin (uniqueDiffWithinAt_Iio K)

end Work.LinnikAreas.A5
