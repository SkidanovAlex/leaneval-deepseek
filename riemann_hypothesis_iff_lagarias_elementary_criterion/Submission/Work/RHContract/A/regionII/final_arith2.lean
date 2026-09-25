import Mathlib

namespace Work.RHContract.A.regionII

/-- One-variable arithmetic inequality closing the Region II `Net₂ ≥ 0` argument (corrected
constants): for `11.5 ≤ L ≤ 19`,
`(1/3)(L/2 + 0.139762)·(0.00528/L) ≤ K(L)·ν(L)` where
`K(L) = (0.071683 L + 0.09036)/((L + 0.094048)(L/2 + 0.139762))` and
`ν(L) = 0.2589 − 0.490129/L − 0.4438/(L − 7.5)`.
Equivalently (clearing the positive denominators `L`, `L + 0.094048`, `L/2 + 0.139762`, `L − 7.5`),
a polynomial inequality of degree 4 on `[11.5,19]`; the minimum of the ratio is `1.5653`,
attained at `L = 11.5`.  The sibling file `RHContract/A/regionII/final_arith.lean` proves the
same statement with `2605/10000` in place of `2589/10000`, so the identical proof technique
(`field_simp` + `nlinarith`) works. -/
theorem final_arith2 (L : ℝ) (h1 : (115 / 10 : ℝ) ≤ L) (h2 : L ≤ 19) :
    (1 / 3) * (L / 2 + 139762 / 1000000) * ((528 / 100000) / L)
      ≤ ((71683 / 1000000 * L + 90360 / 1000000) /
            ((L + 94048 / 1000000) * (L / 2 + 139762 / 1000000)))
        * (2589 / 10000 - (490129 / 1000000) / L - (4438 / 10000) / (L - 15 / 2)) := by
  have hL0 : 0 < L := by linarith
  have hLm : 0 < L - 15 / 2 := by linarith
  have hLc : 0 < L + 94048 / 1000000 := by linarith
  have ha : 0 < L / 2 + 139762 / 1000000 := by linarith
  have hp : (0 : ℝ) < L * 2 - 15 := by linarith
  field_simp
  field_simp [hp.ne']
  have ht : (0 : ℝ) ≤ L - 115 / 10 := by linarith
  have hv : (0 : ℝ) ≤ 19 - L := by linarith
  have ht2 : (0 : ℝ) ≤ (L - 115 / 10) ^ 2 := sq_nonneg _
  have h4 : (0 : ℝ) ≤ (L - 115 / 10) ^ 2 * (19 - L) := mul_nonneg (sq_nonneg _) hv
  have h5 : (0 : ℝ) ≤ (L - 115 / 10) ^ 3 * (19 - L) :=
    mul_nonneg (mul_nonneg (sq_nonneg _) ht) hv
  nlinarith [ht, hv, ht2, h4, h5]

end Work.RHContract.A.regionII
