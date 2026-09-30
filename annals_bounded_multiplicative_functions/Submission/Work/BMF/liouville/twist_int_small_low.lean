import Mathlib
import Submission.Work.BMF.liouville.twist_small_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.liouville

open MeasureTheory

/-- Low-frequency part of `twist_int_bound_small`. For `0 < |u| ≤ 1`,
`∫_3^{max 3 exp(1/|u|)} t⁻¹ H(log t) dt ≤ log(1/|u|) + 2`
where `H(s) = (1+1/s)/s` (`Work.BMF.liouville.Hw`).

Route: `t⁻¹ H(log t) = 1/(t log t) + 1/(t log²t)`, whose antiderivative is
`log log t - 1/log t`.  So the integral equals
`(log log S - 1/log S) - (log log 3 - 1/log 3)` with `S = max 3 exp(1/|u|)`.
If `S = 3` it is `0`.  Otherwise `S = exp(1/|u|)`, `log S = 1/|u|`, and the value is
`log(1/|u|) - |u| - log log 3 + 1/log 3 ≤ log(1/|u|) + 1`
since `log 3 > 1` (so `log log 3 > 0` and `1/log 3 < 1`) and `|u| > 0`. -/
theorem twist_int_small_low (u : ℝ) (hu : 0 < |u|) (hu1 : |u| ≤ 1) :
    ∫ t in (3:ℝ)..(max 3 (Real.exp (1/|u|))), t⁻¹ * Work.BMF.liouville.Hw (Real.log t) ≤
      Real.log (1/|u|) + 2 := by
  set S := max 3 (Real.exp (1/|u|)) with hSdef
  have h3S : (3:ℝ) ≤ S := le_max_left _ _
  -- The antiderivative `F t = log log t - 1/log t` has derivative `t⁻¹ * Hw (log t)`
  -- on `(0, ∞)` (in particular on `[3, S]`).
  have hderiv : ∀ x ∈ Set.Icc (3:ℝ) S,
      HasDerivAt (fun t => Real.log (Real.log t) - (Real.log t)⁻¹) (x⁻¹ * Hw (Real.log x)) x := by
    intro x hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    have hlx : 0 < Real.log x := Real.log_pos (by linarith [hx.1])
    have h1 : HasDerivAt (fun t => Real.log (Real.log t)) (x⁻¹ / Real.log x) x :=
      (Real.hasDerivAt_log hx0).log (ne_of_gt hlx)
    have h2 : HasDerivAt (fun t => (Real.log t)⁻¹) (-(x⁻¹) / (Real.log x)^2) x :=
      (Real.hasDerivAt_log hx0).inv (ne_of_gt hlx)
    have h := h1.sub h2
    convert h using 1
    rw [Hw_eq (ne_of_gt hlx)]
    field_simp
    ring
  -- The integrand is continuous on `[3, S]` (where `t > 0` and `log t > 0`).
  have hcont : ContinuousOn (fun t => t⁻¹ * Hw (Real.log t)) (Set.Icc (3:ℝ) S) := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlt : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith [ht.1]))
    have hHw : ContinuousAt Hw (Real.log t) := (hasDerivAt_Hw hlt).continuousAt
    exact ((continuousAt_id.inv₀ ht0).mul (hHw.comp (Real.continuousAt_log ht0))).continuousWithinAt
  have hcontU : ContinuousOn (fun t => t⁻¹ * Hw (Real.log t)) (Set.uIcc (3:ℝ) S) := by
    rw [Set.uIcc_of_le h3S]; exact hcont
  have hint : IntervalIntegrable (fun t => t⁻¹ * Hw (Real.log t)) volume (3:ℝ) S :=
    hcontU.intervalIntegrable
  have hderiv' : ∀ x ∈ Set.uIcc (3:ℝ) S,
      HasDerivAt (fun t => Real.log (Real.log t) - (Real.log t)⁻¹) (x⁻¹ * Hw (Real.log x)) x := by
    rw [Set.uIcc_of_le h3S]; exact hderiv
  have hFTC : ∫ t in (3:ℝ)..S, t⁻¹ * Hw (Real.log t) =
      (Real.log (Real.log S) - (Real.log S)⁻¹) - (Real.log (Real.log 3) - (Real.log 3)⁻¹) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv' hint
  rw [hFTC]
  by_cases hE : Real.exp (1/|u|) ≤ 3
  · -- Then `S = 3`, the integral vanishes.
    have hS3 : S = 3 := max_eq_left hE
    rw [hS3]
    have h1u : 1 ≤ 1/|u| := by rw [one_div]; exact (one_le_inv₀ hu).mpr hu1
    have hl : 0 ≤ Real.log (1/|u|) := Real.log_nonneg h1u
    linarith
  · -- Then `S = exp(1/|u|)`, `log S = 1/|u|`.
    push Not at hE
    have hSE : S = Real.exp (1/|u|) := max_eq_right (le_of_lt hE)
    rw [hSE]
    have hlogS : Real.log (Real.exp (1/|u|)) = 1/|u| := Real.log_exp _
    rw [hlogS]
    have hinv : (1/|u|)⁻¹ = |u| := by rw [one_div, inv_inv]
    rw [hinv]
    have hlog3 : 1 < Real.log 3 := by
      rw [← Real.log_exp 1]
      exact Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
    have hloglog3 : 0 < Real.log (Real.log 3) := Real.log_pos hlog3
    have hinv3 : (Real.log 3)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hlog3
    linarith [hu, hloglog3, hinv3]

end Work.BMF.liouville
