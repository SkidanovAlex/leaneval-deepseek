import Mathlib
import Submission.Work.ANum.ACertD
import Submission.Work.CNum.CosP_tail
import Submission.Work.CNum.SinP_tail

/-!
# `Work.ANum.rotGlue`

The analytic glue shared by the five rectangle enclosures of `Work.ANum.rotEncl`:
`rot t = exp (2πit)` read off in real coordinates, and the passage from the 11-term Taylor
partial sums `cosP`/`sinP` (`Work.CNum`) to `cos`/`sin` on the angle range `[0, π/4]`
(all the Theorem-A rotation angles lie in that range, so no range reduction is needed).

The numeric content (the actual rational evaluations) lives in `rotEncl`.
-/

namespace Work.ANum

open Submission.CDTPlan Complex Work.CNum
open scoped BigOperators

/-- `rot t = exp (2πit)` written with the real angle in front. -/
lemma rot_eq (t : ℝ) : rot t = Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) := by
  simp only [rot]
  congr 1
  push_cast
  ring

lemma exp_ofReal_mul_I_re (x : ℝ) : (Complex.exp ((x : ℂ) * Complex.I)).re = Real.cos x := by
  rw [Complex.exp_mul_I]
  simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.sin_ofReal_im]

lemma exp_ofReal_mul_I_im (x : ℝ) : (Complex.exp ((x : ℂ) * Complex.I)).im = Real.sin x := by
  rw [Complex.exp_mul_I]
  simp [Complex.cos_ofReal_im, Complex.sin_ofReal_re, Complex.sin_ofReal_im]

lemma rot_re (t : ℝ) : (rot t).re = Real.cos (2 * Real.pi * t) := by
  rw [rot_eq]
  exact exp_ofReal_mul_I_re (2 * Real.pi * t)

lemma rot_im (t : ℝ) : (rot t).im = Real.sin (2 * Real.pi * t) := by
  rw [rot_eq]
  exact exp_ofReal_mul_I_im (2 * Real.pi * t)

lemma rot_neg_re (t : ℝ) : (rot (-t)).re = (rot t).re := by
  rw [rot_re, rot_re, show 2 * Real.pi * (-t) = -(2 * Real.pi * t) by ring, Real.cos_neg]

lemma rot_neg_im (t : ℝ) : (rot (-t)).im = -(rot t).im := by
  rw [rot_im, rot_im, show 2 * Real.pi * (-t) = -(2 * Real.pi * t) by ring, Real.sin_neg]

/-- `cos x ≥ cosP r 11` for `0 ≤ x ≤ r ≤ π/4` (cos is decreasing; the partial sum
underestimates `cos r` by at most `2/24!`). -/
lemma cosP_le_cos {x r : ℝ} (hx0 : 0 ≤ x) (hxr : x ≤ r) (hr4 : r ≤ Real.pi / 4) :
    cosP r 11 ≤ Real.cos x :=
  ((CosP_tail (le_trans hx0 hxr) hr4).1).trans
    (Real.cos_le_cos_of_nonneg_of_le_pi hx0 (by linarith [Real.pi_pos]) hxr)

/-- `cos x ≤ cosP q 11 + 2/24!` for `0 ≤ q ≤ x ≤ π/4`. -/
lemma cos_le_cosP {q x : ℝ} (hq0 : 0 ≤ q) (hqx : q ≤ x) (hx4 : x ≤ Real.pi / 4) :
    Real.cos x ≤ cosP q 11 + 2 * ((Nat.factorial 24 : ℝ))⁻¹ :=
  (Real.cos_le_cos_of_nonneg_of_le_pi hq0 (by linarith [Real.pi_pos]) hqx).trans
    (CosP_tail hq0 (le_trans hqx hx4)).2

/-- `sin x ≥ sinP q 11` for `0 ≤ q ≤ x ≤ π/4`. -/
lemma sinP_le_sin {q x : ℝ} (hq0 : 0 ≤ q) (hqx : q ≤ x) (hx4 : x ≤ Real.pi / 4) :
    sinP q 11 ≤ Real.sin x :=
  ((SinP_tail hq0 (le_trans hqx hx4)).1).trans
    (Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos]) hqx)

/-- `sin x ≤ sinP r 11 + 2/25!` for `0 ≤ x ≤ r ≤ π/4`. -/
lemma sin_le_sinP {x r : ℝ} (hx0 : 0 ≤ x) (hxr : x ≤ r) (hr4 : r ≤ Real.pi / 4) :
    Real.sin x ≤ sinP r 11 + 2 * ((Nat.factorial 25 : ℝ))⁻¹ :=
  (Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos]) hxr).trans
    (SinP_tail (le_trans hx0 hxr) hr4).2

end Work.ANum
