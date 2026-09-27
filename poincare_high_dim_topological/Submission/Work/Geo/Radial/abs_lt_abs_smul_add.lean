import Mathlib
import Submission.Work.Geo.Radial.Basic

namespace Work.Geo.Radial

open Set Metric
open Work.Geo.Radial

/-- Coordinatewise lower bound for a convex blend: if `y` has a coordinate with `|y i| > β` and
`z` is within `δ` of `y` coordinatewise, with `δ < β - m`, then any convex combination
`t • z + (1 - t) • y` (`0 ≤ t ≤ 1`) has that coordinate strictly larger in absolute value than
the coordinate of any `q` with `|q i| ≤ m`. -/
theorem abs_lt_abs_smul_add {n : ℕ} {β δ m t : ℝ} {y z q : PL.E n}
    (hδ : δ < β - m) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hq : ∀ i, |q i| ≤ m)
    (hz : ∀ i, |z i - y i| < δ) {i : Fin n} (hy : β < |y i|) :
    |q i| < |(t • z + (1 - t) • y) i| := by
  set w : PL.E n := t • z + (1 - t) • y with hw
  -- the `i`-th coordinate of the blend is an ordinary convex combination of the coordinates
  have hcoord : w i = t * z i + (1 - t) * y i := by simp [hw]
  -- whence `w i - y i = t * (z i - y i)`
  have hsub : w i - y i = t * (z i - y i) := by rw [hcoord]; ring
  -- so the coordinate of `w` stays within `δ` of the one of `y`
  have hbound : |w i - y i| ≤ δ := by
    rw [hsub, abs_mul]
    have ht : |t| ≤ 1 := abs_le.mpr ⟨by linarith, ht1⟩
    calc |t| * |z i - y i| ≤ 1 * δ :=
          mul_le_mul ht (le_of_lt (hz i)) (abs_nonneg _) (by norm_num)
      _ = δ := one_mul δ
  -- reverse triangle inequality
  have htri : |y i| - |w i| ≤ |w i - y i| := by
    rw [← abs_sub_comm (y i) (w i)]
    exact abs_sub_abs_le_abs_sub _ _
  have hkey : m < |w i| := by linarith
  exact lt_of_le_of_lt (hq i) hkey

end Work.Geo.Radial
