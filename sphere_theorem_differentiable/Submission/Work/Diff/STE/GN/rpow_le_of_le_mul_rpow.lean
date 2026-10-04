import Mathlib
import Submission.Work.Diff.STE.Torus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.GN

theorem rpow_le_of_le_mul_rpow {A C p : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hp : 2 ≤ p)
    (h : A ≤ C * A ^ ((p - 2) / p)) : A ^ (2 / p) ≤ C := by
  have hp0 : p ≠ 0 := by linarith
  -- The exponent identity `(p-2)/p + 2/p = 1` behind the whole estimate.
  have hsplit : (p - 2) / p + 2 / p = 1 := by
    rw [← add_div, sub_add_cancel, div_self hp0]
  rcases eq_or_lt_of_le hA with hA0 | hApos
  · -- `A = 0`: both sides degenerate.
    rw [← hA0, Real.zero_rpow (div_ne_zero two_ne_zero hp0)]
    exact hC
  · -- `A > 0`: multiply `h` by `A ^ (2/p)` and use `A ^ ((p-2)/p) * A ^ (2/p) = A`.
    have hkey : A ^ ((p - 2) / p) * A ^ (2 / p) = A := by
      rw [← Real.rpow_add hApos, hsplit, Real.rpow_one]
    have h1 : A * A ^ (2 / p) ≤ C * A ^ ((p - 2) / p) * A ^ (2 / p) :=
      mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hA _)
    have h2 : C * A ^ ((p - 2) / p) * A ^ (2 / p) = C * A := by
      rw [mul_assoc, hkey]
    have h3 : A * A ^ (2 / p) = A ^ (2 / p) * A := by ring
    rw [h3, h2] at h1
    exact le_of_mul_le_mul_right h1 hApos

end Work.Diff.STE.GN
