import Mathlib
import Submission.Work.CNum.sin_sub_sin_ge

/-!
# A lower bound for `sin ur - sin θ` on `[0, π/4]`

For `0 ≤ θ ≤ ur ≤ π/4` with `ur - θ ≥ 2⁻⁴¹`, the difference `sin ur - sin θ`
is at least `4 / 25!`.

The quantitative content comes from the mean-value-type estimate
`Work.CNum.sin_sub_sin_ge`: `(ur - θ) / 4 ≤ sin ur - sin θ`, which holds on
`[0, π/4]`.  Since `2⁻⁴¹ / 4 = 2⁻⁴³ ≫ 4 / 25!`, the required constant is
easily met; the numerical comparison is discharged by `norm_num`
(`2⁴⁵ ≤ 25!`).
-/

namespace Work.CNum.ExpAux

theorem sin_sub_sin_lower {θ ur : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ ur) (h2 : ur ≤ Real.pi / 4)
    (h3 : ((2:ℝ)^41)⁻¹ ≤ ur - θ) :
    4 * ((Nat.factorial 25 : ℝ))⁻¹ ≤ Real.sin ur - Real.sin θ := by
  have hge : (ur - θ) / 4 ≤ Real.sin ur - Real.sin θ :=
    Work.CNum.sin_sub_sin_ge h0 h1 h2
  have hnum : 4 * ((Nat.factorial 25 : ℝ))⁻¹ ≤ ((2:ℝ)^41)⁻¹ / 4 := by norm_num
  have h4 : ((2:ℝ)^41)⁻¹ / 4 ≤ (ur - θ) / 4 := by linarith
  linarith

end Work.CNum.ExpAux
