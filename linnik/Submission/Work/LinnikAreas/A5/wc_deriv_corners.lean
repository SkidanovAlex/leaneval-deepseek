import Mathlib
import Submission.Work.LinnikAreas.A5.Weights
import Submission.Work.LinnikAreas.A5.Basic
import Submission.Work.LinnikAreas.A5.wc_not_continuousAt_zero
import Submission.Work.LinnikAreas.A5.wc_derivWithin_left
import Submission.Work.LinnikAreas.A5.wc_derivWithin_right

namespace Work.LinnikAreas.A5

/-- **Derivative of the test weight `wc` at the two corners of its support.**

`wc K lam` is the normalised test function of HB Lemma 13.3, cut off at `t = 0`:
it equals `(sinh (Kλ))⁻¹ · sinh((K-t)λ)` on `[0,K]` and `0` outside.  It is smooth on
the *open* interval `(0,K)` (see `wc_deriv_Ioo`), but at both endpoints it has a genuine
corner: at `t = 0` the function jumps (left value `0`, right value `1`) and at `t = K` the
one-sided derivatives differ (left `-λ/sinh(Kλ) ≠ 0`, right `0`).  Hence `wc K lam` is not
differentiable there, and Mathlib's totalised `deriv` takes the default value `0` at
non-differentiable points.

The two conjuncts are proved independently:
* at `0`, `wc K lam` is not even continuous (`wc_not_continuousAt_zero`); differentiability
  would force continuity, so `deriv = 0`;
* at `K`, the left and right within-derivatives (`wc_derivWithin_left`, `wc_derivWithin_right`)
  are `-(sinh (Kλ))⁻¹ λ` and `0`; they differ (using `0 < λ`), so `wc K lam` is not
  differentiable at `K`, and again `deriv = 0`. -/
theorem wc_deriv_corners (K lam : ℝ) (hK : 0 < K) (hlam : 0 < lam) :
    deriv (Work.LinnikAreas.A5.wc K lam) 0 = 0 ∧
    deriv (Work.LinnikAreas.A5.wc K lam) K = 0 := by
  have hnc : ¬ ContinuousAt (wc K lam) 0 := wc_not_continuousAt_zero K lam hK hlam
  refine ⟨deriv_zero_of_not_differentiableAt (fun hd => hnc hd.continuousAt), ?_⟩
  apply deriv_zero_of_not_differentiableAt
  intro hd
  have hleft : deriv (wc K lam) K = -(Real.sinh (K * lam))⁻¹ * lam := by
    have h := (hd.hasDerivAt.hasDerivWithinAt (s := Set.Iio K)).derivWithin
      (uniqueDiffWithinAt_Iio K)
    rw [← h]; exact wc_derivWithin_left K lam hK
  have hright : deriv (wc K lam) K = 0 := by
    have h := (hd.hasDerivAt.hasDerivWithinAt (s := Set.Ioi K)).derivWithin
      (uniqueDiffWithinAt_Ioi K)
    rw [← h]; exact wc_derivWithin_right K lam hK
  have hpos : 0 < (Real.sinh (K * lam))⁻¹ * lam :=
    mul_pos (inv_pos.mpr (Real.sinh_pos_iff.mpr (by positivity))) hlam
  rw [hright] at hleft
  linarith

end Work.LinnikAreas.A5
