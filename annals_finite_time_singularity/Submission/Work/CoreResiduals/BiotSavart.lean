/-
# `Work.CoreResiduals.BiotSavart` — the Biot–Savart chapter of this area

The analytic content of residuals **R2** and **R3** is the regularity of the Biot–Savart operator

  `BS ω x = (4π)⁻¹ ∫ (ω y ⨯ (x-y)) ‖x-y‖⁻³ dy`

on `ℝ³`.  This directory builds the part of that chapter which is within reach, and names the part
which is not:

| result | module |
|---|---|
| `biotSavart_add`, `biotSavart_smul` — **linearity** of `BS` | `BiotSavart.biotSavart_add`, `BiotSavart.biotSavart_smul` |
| `biotSavart_centered` — the integrand is supported in `B(x,ρ)` for `R + ‖x‖ ≤ ρ` | `BiotSavart.biotSavart_centered` |
| `constant_vec_integral_ball_bsK_eq_zero` — the **odd-kernel cancellation** | `BiotSavart.constant_vec_integral_ball_bsK_eq_zero` |
| `biotSavart_centred_sub` — the **regularised form** `BS ω x = (4π)⁻¹∫_{B(x,ρ)} BS(ω - ω x)` | `BiotSavart.biotSavart_centred_sub` |
| `biotSavart_contDiffOn_far` — the **far-field half** of `C¹` (`‖x‖ > 2R`) | `BiotSavart.biotSavart_contDiffOn_far` |
| `biotSavart_contDiff_one` — **`C¹` of `BS ω` for `ω ∈ L^∞ ∩ C^{0,c}_c`**, `c > 0` (the missing chapter) | `BiotSavart.biotSavart_contDiff_one` |

The two named inputs of `Defs.lean` (`BiotSavartSpacetimeC1` for R3, `BiotSavartSpaceTime α` for
R2) are the *space-time* forms of the last row plus the uniformity in `t`; the four proved rows
above are their `x`-regularity core, and the far-field row is the part of the statement that needs
no cancellation at all.  What remains for a full proof of the two inputs is the quantitative
Schauder bound (the Calderón–Zygmund operator `ω ↦ (BS ω, ∇BS ω)` is bounded on the joint Hölder
space) — the standard route is: `biotSavart_centred_sub` to remove the singularity, the Hölder
continuity of `ω` to dominate the differentiated integrand by `C‖x-a‖^{c-3}`, and
differentiation under the integral sign (`hasFDerivAt_integral_of_dominated_loc_of_lip`).
-/
import Mathlib.Tactic.MinImports
import Submission.Work.CoreResiduals.BiotSavart.biotSavart_add
import Submission.Work.CoreResiduals.BiotSavart.biotSavart_smul
import Submission.Work.CoreResiduals.BiotSavart.biotSavart_centered
import Submission.Work.CoreResiduals.BiotSavart.constant_vec_integral_ball_bsK_eq_zero
import Submission.Work.CoreResiduals.BiotSavart.biotSavart_centred_sub
import Submission.Work.CoreResiduals.BiotSavart.biotSavart_contDiffOn_far
import Submission.Work.CoreResiduals.BiotSavart.biotSavart_contDiff_one
import Submission.Work.CoreResiduals.BiotSavart.biotSavartSpaceTime_holds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
