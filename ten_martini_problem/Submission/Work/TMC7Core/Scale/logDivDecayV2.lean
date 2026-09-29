import Mathlib

namespace Work.TMC7Core.Scale

/-- The function `x ↦ (1 + log x)/x` is antitone on `[1, ∞)`.

Proof: write `x = M * r` with `r = x / M ≥ 1`.  Since `M ≥ 1` we have `log M ≥ 0`, and
`log r ≤ r - 1 ≤ (r - 1) * (1 + log M)` because `r - 1 ≥ 0`.  Dividing by the positive
quantity `M * r` turns the desired inequality into exactly this estimate. -/
theorem logDivDecayV2 {M x : ℝ} (hM : 1 ≤ M) (hx : M ≤ x) :
    (1 + Real.log x) / x ≤ (1 + Real.log M) / M := by
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hxpos : 0 < x := lt_of_lt_of_le hMpos hx
  set r : ℝ := x / M with hr
  have hr1 : 1 ≤ r := by
    rw [hr, le_div_iff₀ hMpos]
    linarith
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  have hxeq : x = M * r := by
    rw [hr]
    exact (mul_div_cancel₀ x hMpos.ne').symm
  have hlogx : Real.log x = Real.log M + Real.log r := by
    rw [hxeq, Real.log_mul hMpos.ne' hrpos.ne']
  rw [div_le_div_iff₀ hxpos hMpos]
  rw [hlogx, hxeq]
  have hkey : 1 + (Real.log M + Real.log r) ≤ (1 + Real.log M) * r := by
    have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM
    have hlogr : Real.log r ≤ r - 1 := Real.log_le_sub_one_of_pos hrpos
    have hprod : 0 ≤ (r - 1) * Real.log M := mul_nonneg (by linarith) hlogM
    nlinarith [hlogr, hprod]
  calc (1 + (Real.log M + Real.log r)) * M ≤ ((1 + Real.log M) * r) * M := by
        exact (mul_le_mul_iff_of_pos_right hMpos).mpr hkey
    _ = (1 + Real.log M) * (M * r) := by ring

end Work.TMC7Core.Scale
