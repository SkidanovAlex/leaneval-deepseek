import Mathlib
import Submission.Work.C7.gsetup

namespace Work.C7

/-! The `x`-side ODE verified directly for the candidate right-hand side `R₁ = 2y − w·L` of the
pullback of `B₂`: here `y = Work.C7.yps = x²/(x−1)`, `w = Work.C7.cfun = x − φ = x(x−2)/(x−1)`,
`L = Work.C7.Lps = log(1−x)`.

With `u = (x−1)⁻¹` one has (all in `Submission.Work.C7.gsetup`):
`y(4−y) = −w²`, `y' = w·u`, `w = x(x−2)u`, `w' = (2x−2)u − w·u`, `L' = u`, `2x = w + y`.
Expanding `x(2−x)R₁' − (2−y)R₁ − y²` the coefficient of `L` is `−x(2−x)w' + (2−y)w` (vanishes
by `2x = w+y`), and the `L`-free part cancels as well. Both objects are in `ℚ⟦x⟧`, so this is a
pure `ring`-level computation after rewriting `deriv_cfun`, `deriv_Lps_gU`, `cfun_eq`, `yps_eq`
and clearing the single denominator with `gU_mul : u·(x−1) = 1` (no division by a non-unit is
needed). -/
theorem P1_zero :
    PowerSeries.X * (2 - PowerSeries.X)
      * PowerSeries.derivative (R := ℚ) (2 * Work.C7.yps - Work.C7.cfun * Work.C7.Lps)
      = (2 - Work.C7.yps) * (2 * Work.C7.yps - Work.C7.cfun * Work.C7.Lps)
        + Work.C7.yps ^ 2 := by
  -- `R₁ = 2y − w·L`; expand `R₁' = 2y' − (w'·L + w·L')` using the gsetup derivatives.
  have h1 : PowerSeries.derivative (R := ℚ) (2 * Work.C7.yps) = 2 * (Work.C7.cfun * Work.C7.gU) := by
    rw [show (2 : PowerSeries ℚ) = PowerSeries.C 2 from rfl, Derivation.leibniz,
      PowerSeries.derivative_C, smul_zero, add_zero, smul_eq_mul, Work.C7.deriv_yps]
  have h2 : PowerSeries.derivative (R := ℚ) (Work.C7.cfun * Work.C7.Lps)
      = ((2 * PowerSeries.X - 2) * Work.C7.gU - Work.C7.cfun * Work.C7.gU) * Work.C7.Lps
        + Work.C7.cfun * Work.C7.gU := by
    rw [Work.Pure.b4_deriv_mul, Work.C7.deriv_cfun, Work.C7.deriv_Lps_gU]
    ring
  rw [map_sub, h1, h2, Work.C7.yps_eq, Work.C7.cfun_eq]
  -- The residual difference is `(4x²u − 2x²(x−2)u·L)·(u(x−1) − 1)`, which vanishes since
  -- `u = (x−1)⁻¹` is the inverse of `x−1`.
  linear_combination (4 * PowerSeries.X ^ 2 * Work.C7.gU
    - 2 * PowerSeries.X ^ 2 * (PowerSeries.X - 2) * Work.C7.gU * Work.C7.Lps) * Work.C7.gU_mul

end Work.C7
