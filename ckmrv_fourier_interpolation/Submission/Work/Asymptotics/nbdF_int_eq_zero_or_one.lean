import Mathlib

namespace Work.Asymptotics

/-- If `x ∈ (-1/16, 1 + 1/16)` and an integer `d` satisfies `(d - x)^2 < 7/16`,
then `d` is `0` or `1`. -/
theorem nbdF_int_eq_zero_or_one {x : ℝ} (h1 : -(1 / 16 : ℝ) < x) (h2 : x < 1 + 1 / 16)
    {d : ℤ} (hd : ((d : ℝ) - x) ^ 2 < 7 / 16) : d = 0 ∨ d = 1 := by
  have hnonneg : 0 ≤ d := by
    by_contra hneg
    have hlt : d < 0 := not_le.mp hneg
    have hd1 : d ≤ -1 := by omega
    have hle : (d : ℝ) ≤ -1 := by exact_mod_cast hd1
    nlinarith [sq_nonneg ((d : ℝ) - x + 15 / 16)]
  have hle1 : d ≤ 1 := by
    by_contra hgt
    have hgt' : 1 < d := not_le.mp hgt
    have hd2 : 2 ≤ d := by omega
    have hge : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd2
    nlinarith [sq_nonneg ((d : ℝ) - x - 15 / 16)]
  omega

end Work.Asymptotics
