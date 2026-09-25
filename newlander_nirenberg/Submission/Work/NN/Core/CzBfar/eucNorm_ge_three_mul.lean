import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmCZDefs
import Submission.Work.CR.Flat.Cauchy.bmDzKernel_cz_bound
import Submission.Work.CR.Flat.Cauchy.bmCz.czAux

namespace Work.NN.Core.CzBfar

/-- If `‖z‖` is at least `4*(√n * (R+1)) + 4` and `‖z + x‖ < r` with `R ≤ r ≤ R+1`,
then `x` is far from the origin in the Euclidean norm: `3*r ≤ eucNorm x`. -/
theorem eucNorm_ge_three_mul {n : ℕ} (hn : 0 < n) {R r : ℝ} (hR : 0 ≤ R) (hRr : R ≤ r)
    (hrR1 : r ≤ R + 1) {z x : Fin n → ℂ}
    (hz : 4 * (Real.sqrt n * (R + 1)) + 4 ≤ ‖z‖) (hx : ‖z + x‖ < r) :
    3 * r ≤ Work.CR.Flat.Cauchy.eucNorm x := by
  -- reverse triangle: `‖z‖ ≤ ‖z + x‖ + ‖x‖`
  have hz_le : ‖z‖ ≤ ‖z + x‖ + ‖x‖ := by
    have := norm_sub_le (z + x) x
    simpa using this
  -- hence `‖z‖ - r < ‖x‖`
  have hx_gt : ‖z‖ - r < ‖x‖ := by linarith
  -- and so `4*(√n*(R+1)) + 4 - r < eucNorm x`
  have hlow : 4 * (Real.sqrt n * (R + 1)) + 4 - r < Work.CR.Flat.Cauchy.eucNorm x :=
    lt_of_lt_of_le (by linarith) (Work.CR.Flat.Cauchy.pi_norm_le_eucNorm x)
  -- it remains to compare the two bounds
  have hR1 : 0 ≤ R + 1 := by linarith
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt n := by
    rw [Real.one_le_sqrt]; exact_mod_cast hn
  have hkey : 3 * r ≤ 4 * (Real.sqrt n * (R + 1)) + 4 - r := by
    have hmult : R + 1 ≤ Real.sqrt n * (R + 1) :=
      by nlinarith [mul_nonneg (sub_nonneg.mpr hsqrt1) hR1]
    nlinarith [hmult]
  exact le_trans hkey (le_of_lt hlow)

end Work.NN.Core.CzBfar
