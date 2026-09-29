import Mathlib
import Submission.Work.C7.gsetup
import Submission.Work.Pure.b4_psi_rel

namespace Work.C7

/-! The `x`-side ODE verified directly for the candidate right-hand side
`R₃ = (x−φ)·(2Li₂ + ½L²)` of the pullback of `B₄`: here `y = Work.C7.yps = x²/(x−1)`,
`w = cfun = x − φ = x(x−2)/(x−1)`, `L = Work.C7.Lps`, `Li₂ = Work.C7.Li2ps`. The term
`2y − w·L` is the `x`-form of `B₂∘y`.

Route. Write `V = 2Li₂ + ½L²`, `R₃ = w·V`. Expanding
`x(2−x)·R₃' − (2−y)·R₃ − (4−y)·(2y − w·L) + 2y(4−y)` as a `ℚ⟦x⟧`-combination of
`{1, L, L², Li₂}` with rational-function coefficients, each coefficient vanishes:
* the coefficients of `Li₂` and of `L²` give `x(2−x)w' = (2−y)w` (from `2x = w + y`,
  `w = x(x−2)u`, `w' = (2x−2)u − w·u`);
* the coefficient of `L` is `x(2−x)w·Ψ' + (4−y)wL` with `Ψ' = −L(x−2)u/x`; use the proved
  `Work.Pure.b4Psi_rel_two : (X−1)·sympW·Ψ' = (4−sympY)·b4L` (multiply by `u = (x−1)⁻¹`) —
  equivalently `Psi_deriv`, and note `x(2−x) + (x−1)w = 0`;
* the remaining constant part vanishes by `y(4−y) = −w²` and `(x−1)(1−φ') = −(2−y)`.
Note `deriv Li2ps = −Lps/X`: multiply the whole identity by `X` first and use
`Work.C7.deriv_Li2ps : X * deriv Li2ps = −Lps` (`Submission.Work.C7.xdefs`), then cancel
`X ≠ 0` by `mul_eq_zero`. All rational facts are in `Submission.Work.C7.gsetup`. -/
theorem P3_zero :
    PowerSeries.X * (2 - PowerSeries.X)
      * PowerSeries.derivative (R := ℚ) ((PowerSeries.X - Submission.CDT.sympPhi)
          * (2 * Work.C7.Li2ps + PowerSeries.C (1 / 2 : ℚ) * Work.C7.Lps ^ 2))
      = (2 - Work.C7.yps) * ((PowerSeries.X - Submission.CDT.sympPhi)
          * (2 * Work.C7.Li2ps + PowerSeries.C (1 / 2 : ℚ) * Work.C7.Lps ^ 2))
        + (4 - Work.C7.yps) * (2 * Work.C7.yps - Work.C7.cfun * Work.C7.Lps)
        - 2 * Work.C7.yps * (4 - Work.C7.yps) := by
  -- the `x`-side rational facts (no `L`, no `Li₂`): with `u = (x−1)⁻¹`,
  --   `x(2−x)·w' = (2−y)·w` and `(2−x)·(xu − 2) = −(4−y)`
  have hI : PowerSeries.X * (2 - PowerSeries.X)
      * ((2 * PowerSeries.X - 2) * gU - (PowerSeries.X * (PowerSeries.X - 2) * gU) * gU)
      = (2 - PowerSeries.X ^ 2 * gU) * (PowerSeries.X * (PowerSeries.X - 2) * gU) := by
    linear_combination (2 * PowerSeries.X ^ 2 * (PowerSeries.X - 2) * gU) * gU_mul
  have hII : (2 - PowerSeries.X) * (PowerSeries.X * gU - 2) = -(4 - PowerSeries.X ^ 2 * gU) := by
    linear_combination (-2 * PowerSeries.X) * gU_mul
  -- `(2Li₂ + ½L²)' = 2·Li₂' + L·u`
  have hV : PowerSeries.derivative (R := ℚ) (2 * Li2ps + PowerSeries.C (1 / 2 : ℚ) * Lps ^ 2)
      = 2 * PowerSeries.derivative (R := ℚ) Li2ps + Lps * gU := by
    have hC : PowerSeries.C (1 / 2 : ℚ) * (2 : PowerSeries ℚ) = 1 := by
      rw [show (2 : PowerSeries ℚ) = PowerSeries.C (2 : ℚ) from rfl, ← map_mul]; norm_num
    rw [map_add, Work.Pure.b4_deriv_mul, Work.Pure.b4_deriv_mul, PowerSeries.derivative_C,
        deriv_two, PowerSeries.derivative_pow, deriv_Lps_gU]
    ring_nf
    linear_combination (Lps * gU) * hC
  rw [show (PowerSeries.X - Submission.CDT.sympPhi) = cfun from cfun_eq_sympW.symm]
  -- divide by `x` (a nonzerodivisor), keeping only the relation `x·Li₂' = −L`
  apply mul_left_cancel₀ X_ne_zero
  rw [Work.Pure.b4_deriv_mul, hV, deriv_cfun, cfun_eq, yps_eq]
  linear_combination (PowerSeries.X * (2 * Li2ps + PowerSeries.C (1 / 2 : ℚ) * Lps ^ 2)) * hI
    + (PowerSeries.X * (PowerSeries.X * (PowerSeries.X - 2) * gU) * Lps) * hII
    + (2 * (PowerSeries.X * (2 - PowerSeries.X))
        * (PowerSeries.X * (PowerSeries.X - 2) * gU)) * deriv_Li2ps

end Work.C7
